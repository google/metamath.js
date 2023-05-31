

axiom df-if
  param wph: wff ph
  param vx: setvar x
  param cA: class A
  param cB: class B
  assert |- if ( ph , A , B ) = { x | ( ( x e. A /\ ph ) \/ ( x e. B /\ -. ph ) ) }
end
