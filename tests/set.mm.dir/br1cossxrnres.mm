include "cop.mm"
include "cres.mm"
include "cxrn.mm"
include "ccoss.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "xrnres2.mm"
include "cosseqi.mm"
include "breqi.mm"
include "cvv.mm"
include "wb.mm"
include "opex.mm"
include "br1cossres.mm"
include "mp2an.mm"
include "brxrn.mm"
include "el3v1.mm"
include "bi2anan9.mm"
include "an2anr.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "syl5bbr.mm"

theorem br1cossxrnres
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y

  disjoint A u
  disjoint B u
  disjoint C u
  disjoint D u
  disjoint E u
  disjoint R u
  disjoint S u
  disjoint V u
  disjoint W u
  disjoint X u
  disjoint Y u
  assert |- ( ( ( B e. V /\ C e. W ) /\ ( D e. X /\ E e. Y ) ) -> ( <. B , C >. ,~ ( R |X. ( S |` A ) ) <. D , E >. <-> E. u e. A ( ( u S C /\ u R B ) /\ ( u S E /\ u R D ) ) ) )

  proof
    cB
    cC
    cop
    #
    cD
    cE
    cop
    #
    cR
    cS
    cA
    cres
    cxrn
    #
    ccoss
    #
    wbr
    @0
    @1
    cR
    cS
    cxrn
    #
    cA
    cres
    #
    ccoss
    #
    wbr
    #
    cB
    cV
    wcel
    #
    cC
    cW
    wcel
    #
    wa
    #
    cD
    cX
    wcel
    #
    cE
    cY
    wcel
    #
    wa
    #
    wa
    #
    vu
    cv
    #
    cC
    cS
    wbr
    #
    @15
    cB
    cR
    wbr
    #
    wa
    @15
    cE
    cS
    wbr
    #
    @15
    cD
    cR
    wbr
    #
    wa
    wa
    #
    vu
    cA
    wrex
    #
    @0
    @1
    @6
    @3
    @5
    @2
    cA
    cR
    cS
    xrnres2
    cosseqi
    breqi
    @7
    @15
    @0
    @4
    wbr
    #
    @15
    @1
    @4
    wbr
    #
    wa
    #
    vu
    cA
    wrex
    #
    @14
    @21
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    @7
    @25
    wb
    cB
    cC
    opex
    cD
    cE
    opex
    vu
    cA
    @0
    @1
    @4
    cvv
    cvv
    br1cossres
    mp2an
    @14
    @24
    @20
    vu
    cA
    @14
    @24
    @17
    @16
    wa
    #
    @19
    @18
    wa
    #
    wa
    @20
    @10
    @22
    @26
    @13
    @23
    @27
    @8
    @9
    @22
    @26
    wb
    vu
    @15
    cB
    cC
    cR
    cS
    cvv
    cV
    cW
    brxrn
    el3v1
    @11
    @12
    @23
    @27
    wb
    vu
    @15
    cD
    cE
    cR
    cS
    cvv
    cX
    cY
    brxrn
    el3v1
    bi2anan9
    @17
    @16
    @19
    @18
    an2anr
    syl6bb
    rexbidv
    syl5bb
    syl5bbr
end
