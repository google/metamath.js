include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "cxp.mm"
include "cin.mm"
include "wiso.mm"
include "wcel.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrn.mm"
include "adantrr.mm"
include "adantrl.mm"
include "brinxp.mm"
include "syl2anc.mm"
include "sylan.mm"
include "anassrs.mm"
include "bibi2d.mm"
include "ralbidva.mm"
include "pm5.32i.mm"
include "df-isom.mm"
include "3bitr4i.mm"

theorem isores2
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vx: setvar x
  let vy: setvar y


  assert |- ( H Isom R , S ( A , B ) <-> H Isom R , ( S i^i ( B X. B ) ) ( A , B ) )

  proof
    cA
    cB
    cH
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @1
    cH
    cfv
    #
    @2
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wa
    @0
    @3
    @4
    @5
    cS
    cB
    cB
    cxp
    cin
    #
    wbr
    #
    wb
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wa
    cA
    cB
    cR
    cS
    cH
    wiso
    cA
    cB
    cR
    @10
    cH
    wiso
    @0
    @9
    @14
    @0
    @8
    @13
    vx
    cA
    @0
    @1
    cA
    wcel
    #
    wa
    #
    @7
    @12
    vy
    cA
    @16
    @2
    cA
    wcel
    #
    wa
    @6
    @11
    @3
    @0
    @15
    @17
    @6
    @11
    wb
    #
    @0
    cA
    cB
    cH
    wf
    #
    @15
    @17
    wa
    #
    @18
    cA
    cB
    cH
    f1of
    @19
    @20
    wa
    @4
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @18
    @19
    @15
    @21
    @17
    cA
    cB
    @1
    cH
    ffvelrn
    adantrr
    @19
    @17
    @22
    @15
    cA
    cB
    @2
    cH
    ffvelrn
    adantrl
    @4
    @5
    cB
    cB
    cS
    brinxp
    syl2anc
    sylan
    anassrs
    bibi2d
    ralbidva
    ralbidva
    pm5.32i
    vx
    vy
    cA
    cB
    cR
    cS
    cH
    df-isom
    vx
    vy
    cA
    cB
    cR
    @10
    cH
    df-isom
    3bitr4i
end
