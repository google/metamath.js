
axiom df-if
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assert |- if ( ph , A , B ) = { x | ( ( x e. A /\ ph ) \/ ( x e. B /\ -. ph ) ) }
end
