include "crngo.mm"
include "wcel.mm"
include "cablo.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "rngoablo.mm"
include "ablo32.mm"
include "sylan.mm"

theorem rngoa32
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cG: class G
  let cX: class X
  assume ringgcl.1: |- G = ( 1st ` R )
  assume ringgcl.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) G C ) = ( ( A G C ) G B ) )

  proof
    cR
    crngo
    wcel
    cG
    cablo
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    cC
    cX
    wcel
    w3a
    cA
    cB
    cG
    co
    cC
    cG
    co
    cA
    cC
    cG
    co
    cB
    cG
    co
    wceq
    cR
    cG
    ringgcl.1
    rngoablo
    cA
    cB
    cC
    cG
    cX
    ringgcl.2
    ablo32
    sylan
end
