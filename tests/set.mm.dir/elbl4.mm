include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cbl.mm"
include "co.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "cima.mm"
include "csn.mm"
include "wbr.mm"
include "cxr.mm"
include "wb.mm"
include "rpxr.mm"
include "blcomps.mm"
include "sylanl2.mm"
include "simpll.mm"
include "simprr.mm"
include "simplr.mm"
include "w3a.mm"
include "blval2.mm"
include "eleq2d.mm"
include "syl3anc.mm"
include "cop.mm"
include "elimasng.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "ancoms.mm"
include "adantl.mm"
include "3bitrd.mm"

theorem elbl4
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cX: class X


  assert |- ( ( ( D e. ( PsMet ` X ) /\ R e. RR+ ) /\ ( A e. X /\ B e. X ) ) -> ( B e. ( A ( ball ` D ) R ) <-> B ( `' D " ( 0 [,) R ) ) A ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cR
    crp
    wcel
    #
    wa
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    #
    wa
    #
    cB
    cA
    cR
    cD
    cbl
    cfv
    #
    co
    wcel
    #
    cA
    cB
    cR
    @7
    co
    #
    wcel
    #
    cA
    cD
    ccnv
    cc0
    cR
    cico
    co
    cima
    #
    cB
    csn
    cima
    #
    wcel
    #
    cB
    cA
    @11
    wbr
    #
    @1
    @0
    cR
    cxr
    wcel
    @5
    @8
    @10
    wb
    cR
    rpxr
    cB
    cD
    cA
    cR
    cX
    blcomps
    sylanl2
    @6
    @0
    @4
    @1
    @10
    @13
    wb
    @0
    @1
    @5
    simpll
    @2
    @3
    @4
    simprr
    @0
    @1
    @5
    simplr
    @0
    @4
    @1
    w3a
    @9
    @12
    cA
    cD
    cB
    cR
    cX
    blval2
    eleq2d
    syl3anc
    @5
    @13
    @14
    wb
    #
    @2
    @4
    @3
    @15
    @4
    @3
    wa
    @13
    cB
    cA
    cop
    @11
    wcel
    @14
    @11
    cB
    cA
    cX
    cX
    elimasng
    cB
    cA
    @11
    df-br
    syl6bbr
    ancoms
    adantl
    3bitrd
end
