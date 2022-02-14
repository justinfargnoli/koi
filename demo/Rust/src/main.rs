#[derive(Clone)]
enum Nat {
    O,
    S(Box<Nat>)
} 

fn add(n: Nat, m: Nat) -> Nat {
    match n {
        Nat::O => m,
        Nat::S(p) => Nat::S(Box::new(add(*p, m)))
    }
}

fn one_nat() -> Nat {
    Nat::S(Box::new(Nat::O))
}

enum Vector<T> {
    Nil, 
    Cons(T, Nat, Box<Vector<T>>)
}

fn append<T>(_: Nat, p: Nat, v: Vector<T>, w: Vector<T>) -> Vector<T> {
    match v {
        Vector::Nil => w,
        Vector::Cons(a, n0, vector) => Vector::Cons(a, add(n0.clone(), p.clone()), Box::new(append(n0, p, *vector, w)))
    }
}

fn one_vec() -> Vector<Nat> {
    Vector::Cons(Nat::O, one_nat(), Box::new(Vector::Nil))
}

fn main() {
    let two_vec = append(Nat::O, add(one_nat(), one_nat()), one_vec(), one_vec());
}