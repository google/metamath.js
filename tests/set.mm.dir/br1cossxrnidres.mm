include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cid.mm"
include "cres.mm"
include "cxrn.mm"
include "ccoss.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wceq.mm"
include "br1cossxrnres.mm"
include "wb.mm"
include "cvv.mm"
include "ideq2.mm"
include "elv.mm"
include "anbi1i.mm"
include "anbi12i.mm"
include "rexbii.mm"
include "syl6bb.mm"

theorem br1cossxrnidres
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
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
  disjoint V u
  disjoint W u
  disjoint X u
  disjoint Y u
  assert |- ( ( ( B e. V /\ C e. W ) /\ ( D e. X /\ E e. Y ) ) -> ( <. B , C >. ,~ ( R |X. ( _I |` A ) ) <. D , E >. <-> E. u e. A ( ( u = C /\ u R B ) /\ ( u = E /\ u R D ) ) ) )

  proof
    cB
    cV
    wcel
    cC
    cW
    wcel
    wa
    cD
    cX
    wcel
    cE
    cY
    wcel
    wa
    wa
    cB
    cC
    cop
    cD
    cE
    cop
    cR
    cid
    cA
    cres
    cxrn
    ccoss
    wbr
    vu
    cv
    #
    cC
    cid
    wbr
    #
    @0
    cB
    cR
    wbr
    #
    wa
    #
    @0
    cE
    cid
    wbr
    #
    @0
    cD
    cR
    wbr
    #
    wa
    #
    wa
    #
    vu
    cA
    wrex
    @0
    cC
    wceq
    #
    @2
    wa
    #
    @0
    cE
    wceq
    #
    @5
    wa
    #
    wa
    #
    vu
    cA
    wrex
    vu
    cA
    cB
    cC
    cD
    cR
    cid
    cE
    cV
    cW
    cX
    cY
    br1cossxrnres
    @7
    @12
    vu
    cA
    @3
    @9
    @6
    @11
    @1
    @8
    @2
    @1
    @8
    wb
    vu
    @0
    cC
    cvv
    ideq2
    elv
    anbi1i
    @4
    @10
    @5
    @4
    @10
    wb
    vu
    @0
    cE
    cvv
    ideq2
    elv
    anbi1i
    anbi12i
    rexbii
    syl6bb
end
