include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "cxrn.mm"
include "ccoss.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "br1cossxrnres.mm"
include "wb.mm"
include "cvv.mm"
include "brcnvep.mm"
include "elv.mm"
include "anbi1i.mm"
include "anbi12i.mm"
include "rexbii.mm"
include "syl6bb.mm"

theorem br1cossxrncnvepres
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
  assert |- ( ( ( B e. V /\ C e. W ) /\ ( D e. X /\ E e. Y ) ) -> ( <. B , C >. ,~ ( R |X. ( `' _E |` A ) ) <. D , E >. <-> E. u e. A ( ( C e. u /\ u R B ) /\ ( E e. u /\ u R D ) ) ) )

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
    cep
    ccnv
    #
    cA
    cres
    cxrn
    ccoss
    wbr
    vu
    cv
    #
    cC
    @0
    wbr
    #
    @1
    cB
    cR
    wbr
    #
    wa
    #
    @1
    cE
    @0
    wbr
    #
    @1
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
    cC
    @1
    wcel
    #
    @3
    wa
    #
    cE
    @1
    wcel
    #
    @6
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
    @0
    cE
    cV
    cW
    cX
    cY
    br1cossxrnres
    @8
    @13
    vu
    cA
    @4
    @10
    @7
    @12
    @2
    @9
    @3
    @2
    @9
    wb
    vu
    @1
    cC
    cvv
    brcnvep
    elv
    anbi1i
    @5
    @11
    @6
    @5
    @11
    wb
    vu
    @1
    cE
    cvv
    brcnvep
    elv
    anbi1i
    anbi12i
    rexbii
    syl6bb
end
