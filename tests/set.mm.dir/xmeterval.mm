include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cop.mm"
include "ccnv.mm"
include "cr.mm"
include "cima.mm"
include "cxp.mm"
include "wa.mm"
include "wbr.mm"
include "co.mm"
include "w3a.mm"
include "cxr.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "xmetf.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "breqi.mm"
include "df-br.mm"
include "bitri.mm"
include "df-3an.mm"
include "opelxp.mm"
include "bicomi.mm"
include "df-ov.mm"
include "eleq1i.mm"
include "anbi12i.mm"
include "3bitr4g.mm"

theorem xmeterval
  let cA: class A
  let cB: class B
  let cD: class D
  let c.sm: class .~
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  assume xmeter.1: |- .~ = ( `' D " RR )


  assert |- ( D e. ( *Met ` X ) -> ( A .~ B <-> ( A e. X /\ B e. X /\ ( A D B ) e. RR ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cA
    cB
    cop
    #
    cD
    ccnv
    cr
    cima
    #
    wcel
    #
    @1
    cX
    cX
    cxp
    #
    wcel
    #
    @1
    cD
    cfv
    #
    cr
    wcel
    #
    wa
    #
    cA
    cB
    c.sm
    wbr
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    cD
    co
    #
    cr
    wcel
    #
    w3a
    #
    @0
    @4
    cxr
    cD
    wf
    cD
    @4
    wfn
    @3
    @8
    wb
    cD
    cX
    xmetf
    @4
    cxr
    cD
    ffn
    @4
    @1
    cr
    cD
    elpreima
    3syl
    @9
    cA
    cB
    @2
    wbr
    @3
    cA
    cB
    c.sm
    @2
    xmeter.1
    breqi
    cA
    cB
    @2
    df-br
    bitri
    @14
    @10
    @11
    wa
    #
    @13
    wa
    @8
    @10
    @11
    @13
    df-3an
    @15
    @5
    @13
    @7
    @5
    @15
    cA
    cB
    cX
    cX
    opelxp
    bicomi
    @12
    @6
    cr
    cA
    cB
    cD
    df-ov
    eleq1i
    anbi12i
    bitri
    3bitr4g
end
