
axiom df-an(vf: $var$ f, vp: $var$ p, vq: $var$ q) {

  return $|- T. |= [ /\ = \ p : bool . \ q : bool . [ \ f : ( bool -> ( bool -> bool ) ) . [ p : bool f : ( bool -> ( bool -> bool ) ) q : bool ] = \ f : ( bool -> ( bool -> bool ) ) . [ T. f : ( bool -> ( bool -> bool ) ) T. ] ] ]$;
}
