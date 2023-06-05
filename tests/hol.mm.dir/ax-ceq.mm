

axiom ax-ceq(hal: type al, hbe: type be, ta: term A, tb: term B, tf: term F, tt: term T) {
  assume ax-ceq.1: |- "F : ( al -> be )";
  assume ax-ceq.2: |- "T : ( al -> be )";
  assume ax-ceq.3: |- "A : al";
  assume ax-ceq.4: |- "B : al";

  return |- "( ( ( = F ) T ) , ( ( = A ) B ) ) |= ( ( = ( F A ) ) ( T B ) )";
}
