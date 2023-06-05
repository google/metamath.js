

axiom wc(hal: type al, hbe: type be, tf: term F, tt: term T) {
  assume wc.1: |- "F : ( al -> be )";
  assume wc.2: |- "T : al";

  return |- "( F T ) : be";
}
