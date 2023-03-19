include "pjcompi.mm"

theorem pjvi
  let cA: class A
  let cB: class B
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pjfn.1: |- H e. CH


  assert |- ( ( A e. H /\ B e. ( _|_ ` H ) ) -> ( ( projh ` H ) ` ( A +h B ) ) = A )

  proof
    cA
    cB
    cH
    pjfn.1
    pjcompi
end
