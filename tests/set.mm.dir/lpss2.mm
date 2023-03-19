include "lpss3.mm"

theorem lpss2
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  assume lpss2.1: |- X = U. J


  assert |- ( ( J e. Top /\ A C_ X /\ B C_ A ) -> ( ( limPt ` J ) ` B ) C_ ( ( limPt ` J ) ` A ) )

  proof
    cA
    cB
    cJ
    cX
    lpss2.1
    lpss3
end
