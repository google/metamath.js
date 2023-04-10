
axiom ax-inf(vf: $var$ f) {

  return $|- T. |= ( ? \ f : ( ind -> ind ) . [ ( 1-1 f : ( ind -> ind ) ) /\ ( ~ ( onto f : ( ind -> ind ) ) ) ] )$;
}
