package hw5;

import soot.SootMethod;
import soot.Local;
import soot.Unit;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;

import java.util.*;

public class InterSignAnalysis {
    public static Set<Context> worklist;
    public static Set<Context> analyzing;
    public static Map<Context, Summary> results;
    public static Map<Context, Set<Context>> callers;
    private static InterSignAnalysis theInstance = new InterSignAnalysis();

    static {
        worklist = new HashSet<>();
        analyzing = new HashSet<>();
        results = new HashMap<>();
        callers = new HashMap<>();
    }

    /**
     * We're using a singleton pattern here so that analysis results can be
     * looked up as they're collected.
     * e.g.,
     *   InterSignAnalysis.getInstance().callers can be accessed from IntraSignAnalysis
     */
    public static InterSignAnalysis getInstance() {
        return theInstance;
    }

    public static void resetAnalysis() {
        theInstance = new InterSignAnalysis();
    }
    
    //call sites have unique integer to differetiate calling
    private Map<Unit, Integer> callSites = new IdentityHashMap<>();
    private int nextCallSite = 0;

    public int getCallSite(Unit unit){
        if(!callSites.containsKey(unit)){
            callSites.put(unit, nextCallSite);
            nextCallSite++;
        }

        return callSites.get(unit);
    }

    //what is returned value
    public Sigma.L getReturnSign(Context ctx){
        IntraSignAnalysis analysis = intraAnalysis.get(ctx);
        
        //no analysis
        if (analysis == null){
            return Sigma.L.Bottom;
        }
        return analysis.getReturnSign();
    }

    //report warning for each analysis
    private Map<Context, IntraSignAnalysis> intraAnalysis = new HashMap<>();

    public void analyzeProgram(SootMethod main) {
        //initialize all to bottom
        Context prog = new Context(main, new ArrayList<>());
        Sigma input = new Sigma(main.getActiveBody().getLocals(), Sigma.L.Bottom);
        Sigma output = new Sigma(main.getActiveBody().getLocals(), Sigma.L.Bottom);
        results.put(prog, new Summary(input, output));
        worklist.add(prog);

        //while the worklist is not empty, analyze what is on the worklist
        while(!worklist.isEmpty()){
            //get one from worklist
            Iterator<Context> it = worklist.iterator();
            Context curr = it.next();
            it.remove();
            Summary currSummary = results.get(curr);
            
            //analyze the current
            analyzing.add(curr);
            Sigma newOutput = analyze(curr, currSummary.input);
            analyzing.remove(curr);

            //if ouput changed, propagate to caller
            if(!newOutput.equals(currSummary.output)){
                currSummary.output = newOutput;
                Set<Context> currCallers = callers.get(curr);
                if(currCallers != null){
                    worklist.addAll(currCallers);
                }
            }
        }
    }

    Sigma analyze(Context ctx, Sigma sigma_i) {
        // A good strategy will likely involve passing the context and the input
        // sigma to the SignAnalysis and then looking at the results to extract
        // the new sigma.
        
        //cfg, and intialize analysis
        UnitGraph graph = new ExceptionalUnitGraph(ctx.fn.getActiveBody());
        IntraSignAnalysis analysis = new IntraSignAnalysis(graph, ctx, sigma_i);
        analysis.run();
        intraAnalysis.put(ctx, analysis);

        //initialize to bottom
        Sigma output = new Sigma(ctx.fn.getActiveBody().getLocals(), Sigma.L.Bottom);
        boolean firstElem = true;

        for (Unit tail: graph.getTails()){
            Sigma tailSigma = analysis.getFlowAfter(tail);
            //if it is first element, just put it there
            if (firstElem){
                tailSigma.copy(output);
                firstElem = false;
            }else{
                Sigma old = output;
                output = new Sigma();

                Set<Local> locals = new HashSet<>();

                //all variables
                locals.addAll(old.map.keySet());
                locals.addAll(tailSigma.map.keySet());

                //for all variable, update the analysis
                for (Local l : locals){
                    Sigma.L v1 = old.map.get(l);
                    Sigma.L v2 = tailSigma.map.get(l);

                    if(v1 == null){
                        v1 = Sigma.L.Bottom;
                    }

                    output.map.put(l, Sigma.join(v1,v2));
                }
            }
        }
        return output;
    }

    public void reportWarnings() {
        // You may need to keep track of intra-analysis objects for each context
        // in order to go over their dataflow values and report warnings as needed
        for (IntraSignAnalysis analysis : intraAnalysis.values()){
            analysis.reportWarnings();
        }
    }
}
