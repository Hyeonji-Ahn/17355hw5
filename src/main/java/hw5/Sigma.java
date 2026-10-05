package hw5;

import soot.Local;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * A class to represent abstract values at a program point.
 */
public class Sigma {
    /**
     * Abstract values
     */
    enum L {
        Top, Bottom, N, P, Z
    }

    // Maps locals to abstract values
    public Map<Local, L> map;

    /**
     * An empty sigma
     */
    public Sigma() {
        this.map = new HashMap<>();
    }

    /**
     * An initialized sigma
     * @param locals the locals at this point
     * @param initialVal initial value to use
     */
    public Sigma(Iterable<Local> locals, L initialVal) {
        this.map = new HashMap<>();
        for (Local l : locals) {
            this.map.put(l, initialVal);
        }
    }

    public static L signOfInt(int n){
        if (n < 0){
            return L.N;
        }else if (n==0) {
            return L.Z;
        }else{
            return L.P;
        }
    }

    public static L add(L a, L b) {

        if (a == L.Bottom || b == L.Bottom) {
            return L.Bottom;
        }

        if (a == L.Z) {
            return b;
        }

        if (b == L.Z) {
            return a;
        }

        if (a == L.P && b == L.P) {
            return L.P;
        }

        if (a == L.N && b == L.N) {
            return L.N;
        }

        return L.Top;
    }

    public static L negate(L a) {

        if (a == L.P) {
            return L.N;
        }

        if (a == L.N) {
            return L.P;
        }

        return a;
    }

    public static L sub(L a, L b) {
        return add(a, negate(b));
    }

    public static L mul(L a, L b) {

        if (a == L.Bottom || b == L.Bottom) {
            return L.Bottom;
        }

        if (a == L.Z || b == L.Z) {
            return L.Z;
        }

        if (a == L.Top || b == L.Top) {
            return L.Top;
        }

        if (a == b) {
            return L.P;
        }

        return L.N;
    }

    public static L div(L a, L b) {

        if (a == L.Bottom || b == L.Bottom) {
            return L.Bottom;
        }

        if (b == L.Z) {
            return L.Top;
        }

        if (a == L.Z) {
            return L.Z;
        }

        if (a == L.Top || b == L.Top) {
            return L.Top;
        }

        return L.Top;
    }


    /**
     * Join for two abstract values
     */
    public static L join(L v1, L v2) {
        if (v1 == v2){
            return v1;
        }
        if (v1 == L.Bottom){
            return v2;
        }
        if (v2 == L.Bottom){
            return v1;
        }
        return L.Top;
    }

    public String toString() {
        Set<Local> keys = map.keySet();
        StringBuilder str = new StringBuilder("[ ");
        for (Local key : keys) {
            str.append(key.getName()).append(": ").append(map.get(key)).append("; ");
        }
        return str + " ]";
    }

    public void copy(Sigma dest) {
        dest.map = new HashMap<>(map);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj){
            return true;
        }

        if(! (obj instanceof Sigma)){
            return false;
        }

        Sigma compto = (Sigma) obj;
        return this.map.equals(compto.map);
    }

    @Override
    public int hashCode() {
        return this.map.hashCode();
    }
}