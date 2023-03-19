include "wbr.mm"
include "wo.mm"
include "wb.mm"
include "cif.mm"
include "ctsr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wceq.mm"
include "breq2.mm"
include "bibi1d.mm"
include "olc.mm"
include "wi.mm"
include "cps.mm"
include "cdm.mm"
include "cxp.mm"
include "ccnv.mm"
include "cun.mm"
include "wss.mm"
include "eqid.mm"
include "istsr.mm"
include "simplbi.mm"
include "pstr.mm"
include "3expib.mm"
include "syl.mm"
include "adantr.mm"
include "expdimp.mm"
include "impancom.mm"
include "idd.mm"
include "jaod.mm"
include "impbid2.mm"
include "wn.mm"
include "orc.mm"
include "tsrlin.mm"
include "3adant3r1.mm"
include "orcanai.mm"
include "syldan.mm"
include "ifbothda.mm"

theorem tsrlemax
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  assume istsr.1: |- X = dom R


  assert |- ( ( R e. TosetRel /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A R if ( B R C , C , B ) <-> ( A R B \/ A R C ) ) )

  proof
    cB
    cC
    cR
    wbr
    #
    cA
    cC
    cR
    wbr
    #
    cA
    cB
    cR
    wbr
    #
    @1
    wo
    #
    wb
    @2
    @3
    wb
    cA
    @0
    cC
    cB
    cif
    #
    cR
    wbr
    #
    @3
    wb
    cR
    ctsr
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cC
    cB
    cC
    @4
    wceq
    @1
    @5
    @3
    cC
    @4
    cA
    cR
    breq2
    bibi1d
    cB
    @4
    wceq
    @2
    @5
    @3
    cB
    @4
    cA
    cR
    breq2
    bibi1d
    @11
    @0
    wa
    #
    @1
    @3
    @1
    @2
    olc
    @12
    @2
    @1
    @1
    @11
    @2
    @0
    @1
    @11
    @2
    @0
    @1
    @6
    @2
    @0
    wa
    @1
    wi
    #
    @10
    @6
    cR
    cps
    wcel
    #
    @13
    @6
    @14
    cR
    cdm
    #
    @15
    cxp
    cR
    cR
    ccnv
    cun
    wss
    cR
    @15
    @15
    eqid
    istsr
    simplbi
    #
    @14
    @2
    @0
    @1
    cA
    cB
    cC
    cR
    pstr
    3expib
    syl
    adantr
    expdimp
    impancom
    @12
    @1
    idd
    jaod
    impbid2
    @11
    @0
    wn
    #
    wa
    #
    @2
    @3
    @2
    @1
    orc
    @18
    @2
    @2
    @1
    @18
    @2
    idd
    @11
    @17
    cC
    cB
    cR
    wbr
    #
    @1
    @2
    wi
    @11
    @0
    @19
    @6
    @8
    @9
    @0
    @19
    wo
    @7
    cB
    cC
    cR
    cX
    istsr.1
    tsrlin
    3adant3r1
    orcanai
    @11
    @1
    @19
    @2
    @11
    @1
    @19
    @2
    @6
    @1
    @19
    wa
    @2
    wi
    #
    @10
    @6
    @14
    @20
    @16
    @14
    @1
    @19
    @2
    cA
    cC
    cB
    cR
    pstr
    3expib
    syl
    adantr
    expdimp
    impancom
    syldan
    jaod
    impbid2
    ifbothda
end
