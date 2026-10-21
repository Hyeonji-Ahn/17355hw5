package hw5;

import common.ErrorMessage;
import common.Utils;
import soot.Local;
import soot.Unit;
import soot.ValueBox;
import soot.toolkits.graph.DominatorsFinder;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;
import soot.SootMethod;

import soot.jimple.*;
import soot.Value;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.BinaryOperator;

public class IntraSignAnalysis extends ForwardFlowAnalysis<Unit, Sigma> {
    // Holds the set of local variables
    private Set<Local> locals = new HashSet<>();

    // The calling context for the analysis
    // Null if no context (e.g., when only running intraprocedurally)
    private Context ctx;

    // The input sigma for this analysis
    private Sigma sigma_i;

    /**
     * Constructor with no context. This is useful for testing the intraprocedural
     * analysis on its own.
     */
    IntraSignAnalysis(UnitGraph graph) {
        // Note the construction of a default Sigma
        this(graph, null, null);
    }

    /**
     * Allows creating an intra analysis with just the context and the input sigma,
     * since the unit graph can be grabbed from the function in the context.
     */
    IntraSignAnalysis(Context ctx, Sigma sigma_i) {
        this(new ExceptionalUnitGraph(ctx.fn.getActiveBody()), ctx, sigma_i);
    }

    IntraSignAnalysis(UnitGraph graph, Context ctx, Sigma sigma_i) {
        super(graph);
        this.ctx = ctx;
        this.sigma_i = sigma_i;

        // Collect locals
        this.locals.addAll(graph.getBody().getLocals());
    }

    //what each method return
    public Sigma.L getReturnSign(){
        Sigma.L res = Sigma.L.Bottom;
        for(Unit unit : this.graph){
            if(unit instanceof ReturnStmt){ //if there is return
                ReturnStmt ret = (ReturnStmt) unit;
                Sigma before = this.getFlowBefore(unit); 
                Sigma.L sign = valueSign(ret.getOp(), before);
                res = Sigma.join(res, sign); //join the ran outcome and before
            }
        }
        return res;
    }

    private Sigma.L valueSign(Value value, Sigma sigma){
        //in integer format. then convert
        if (value instanceof IntConstant){
            int n = ((IntConstant) value).value;
            return Sigma.signOfInt(n);
        }

        //sign is already there. 
        if(value instanceof Local){
            Sigma.L sign = sigma.map.get((Local) value);

            if (sign == null){
                return Sigma.L.Top;
            }

            return sign;
        }

        //sign is reference
        if(value instanceof ParameterRef){
            ParameterRef paramRef = (ParameterRef) value;

            Local param = ((UnitGraph)this.graph).getBody().getParameterLocal(paramRef.getIndex());
            Sigma.L sign = sigma.map.get(param);

            if (sign == null){
                return Sigma.L.Top;
            }

            return sign;
        }

        //addition
        if(value instanceof AddExpr){
            BinopExpr expr = (BinopExpr) value;

            Sigma.L left = valueSign(expr.getOp1(), sigma);
            Sigma.L right = valueSign(expr.getOp2(), sigma);

            return Sigma.add(left, right);
        }

        // Subtraction
        if (value instanceof SubExpr) {
            BinopExpr expr = (BinopExpr) value;

            Sigma.L left = valueSign(expr.getOp1(), sigma);
            Sigma.L right = valueSign(expr.getOp2(), sigma);

            return Sigma.sub(left, right);
        }

        // Multiplication
        if (value instanceof MulExpr) {
            BinopExpr expr = (BinopExpr) value;

            Sigma.L left = valueSign(expr.getOp1(), sigma);
            Sigma.L right = valueSign(expr.getOp2(), sigma);

            return Sigma.mul(left, right);
        }

        // Division
        if (value instanceof DivExpr) {
            BinopExpr expr = (BinopExpr) value;

            Sigma.L left = valueSign(expr.getOp1(), sigma);
            Sigma.L right = valueSign(expr.getOp2(), sigma);

            return Sigma.div(left, right);
        }

        //default
        return Sigma.L.Top;
    }

    // Runs the analysis
    public void run() {
        this.doAnalysis();
    }

    /**
     * Report warnings. This will use the analysis results collected by the constructor.
     */
    public void reportWarnings() {
        // TODO: Implement this (raise warnings)!
        // TODO: This implementation is incorrect, but it shows how to report a warning
        for (Unit u : this.graph) {
            Sigma sigmaBefore = this.getFlowBefore(u); // TODO: Use this info to decide if a warning is appropriate
            for (ValueBox v : u.getUseAndDefBoxes()){
                Value val = v.getValue();

                if (!(val instanceof ArrayRef)){
                    continue;
                }

                ArrayRef aref = (ArrayRef) val;

                //get sign of array index
                Sigma.L indexSign = valueSign(aref.getIndex(), sigmaBefore);

                //negative index for sure
                if(indexSign == Sigma.L.N){
                    Utils.reportWarning(u, ErrorMessage.NEGATIVE_INDEX_ERROR);
                }

                //can be negative index
                if(indexSign == Sigma.L.Top){
                    Utils.reportWarning(u, ErrorMessage.POSSIBLE_NEGATIVE_INDEX_WARNING);
                }
            }
        }
    }

    /**
     * Run flow function for this unit
     *
     * @param inValue  The initial Sigma at this point
     * @param unit     The current Unit
     * @param outValue The updated Sigma after the flow function
     */
    @Override
    protected void flowThrough(Sigma inValue, Unit unit, Sigma outValue) {
        //copy over
        inValue.copy(outValue);

        //if not assignment, continue
        if (! (unit instanceof DefinitionStmt)){
            return;
        }

        DefinitionStmt stmt = (DefinitionStmt) unit;

        Value left = stmt.getLeftOp();
        Local lhs = (Local) left;
        
        //recognize what right hand side value was stored as
        Value right = stmt.getRightOp();
        Sigma.L rhs;
        //if there is context regarding right handside
        if (right instanceof InvokeExpr && ctx != null){
            InvokeExpr invoke = (InvokeExpr) right;
            
            //where is this from
            SootMethod callee = invoke.getMethod();
            int callSite = InterSignAnalysis.getInstance().getCallSite(unit);
            Context calleeCtx = Context.getCtx(callee, ctx, callSite);
            Sigma calleeIn = new Sigma(callee.getActiveBody().getLocals(), Sigma.L.Bottom);

            //for each argument join everything
            for (int i=0; i<invoke.getArgCount(); i++){
                Local param = callee.getActiveBody().getParameterLocal(i);
                Sigma.L argSign = valueSign(invoke.getArg(i), inValue);
                calleeIn.map.put(param, argSign);
            }
            
            //what is the context
            InterSignAnalysis inter = InterSignAnalysis.getInstance();
            inter.callers.computeIfAbsent(calleeCtx, k -> new HashSet<>()).add(ctx);
            
            //if this context never analyzed before
            if(!inter.results.containsKey(calleeCtx)){
                Sigma calleeOut = new Sigma(callee.getActiveBody().getLocals(), Sigma.L.Bottom);
                inter.results.put(calleeCtx, new Summary(calleeIn, calleeOut));
                inter.worklist.add(calleeCtx);
            }else{
                Summary summary = inter.results.get(calleeCtx);
                //look at all caller that use this
                boolean changed = false;
                for (Local l : calleeIn.map.keySet()){
                    Sigma.L oldV = summary.input.map.get(l);
                    Sigma.L newV = calleeIn.map.get(l);
                    Sigma.L joined = Sigma.join(oldV, newV);

                    if (joined != oldV){
                        summary.input.map.put(l, joined);
                        changed = true;
                    }
                }

                if (changed){
                    inter.worklist.add(calleeCtx);
                }
            }
            rhs = inter.getReturnSign(calleeCtx);

        } else {
            //nothing there. same as intraSignAnalysis
            rhs = valueSign(right, inValue);
        }

        //join
        outValue.map.put(lhs, rhs);
    }

    /**
     * Initial flow information at the start of a method
     */
    @Override
    protected Sigma entryInitialFlow() {
        if (this.sigma_i != null) {
            return this.sigma_i;
        } else {
            return new Sigma(locals, Sigma.L.Bottom);
        }
    }

    /**
     * Initial flow information at each other program point
     */
    @Override
    protected Sigma newInitialFlow() {
        return new Sigma(locals, Sigma.L.Bottom);
    }

    /**
     * Join at a program point lifted to sets
     */
    @Override
    protected void merge(Sigma in1, Sigma in2, Sigma out) {
        for (Local l : locals){
            Sigma.L v1 = in1.map.get(l);
            Sigma.L v2 = in2.map.get(l);

            out.map.put(l, Sigma.join(v1, v2));
        }
    }

    /**
     * Copy for sets
     */
    @Override
    protected void copy(Sigma source, Sigma dest) {
        source.copy(dest);
    }
}
