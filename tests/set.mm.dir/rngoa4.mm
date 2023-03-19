include "crngo.mm"
include "wcel.mm"
include "cablo.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "rngoablo.mm"
include "ablo4.mm"
include "syl3an1.mm"

theorem rngoa4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cG: class G
  let cX: class X
  assume ringgcl.1: |- G = ( 1st ` R )
  assume ringgcl.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ ( A e. X /\ B e. X ) /\ ( C e. X /\ D e. X ) ) -> ( ( A G B ) G ( C G D ) ) = ( ( A G C ) G ( B G D ) ) )

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
    wa
    cC
    cX
    wcel
    cD
    cX
    wcel
    wa
    cA
    cB
    cG
    co
    cC
    cD
    cG
    co
    cG
    co
    cA
    cC
    cG
    co
    cB
    cD
    cG
    co
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
    cD
    cG
    cX
    ringgcl.2
    ablo4
    syl3an1
end
