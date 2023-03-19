include "cpw.mm"
include "wss.mm"
include "wn.mm"
include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "crab.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wceq.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "w3a.mm"
include "simp2r.mm"
include "difss.mm"
include "cvv.mm"
include "wb.mm"
include "cun.mm"
include "ssun1.mm"
include "undif1.mm"
include "sseqtr4i.mm"
include "simpl2r.mm"
include "simpl2l.mm"
include "unexg.mm"
include "syl2anc.mm"
include "ssexg.mm"
include "sylancr.mm"
include "elpw2g.mm"
include "syl.mm"
include "mpbiri.mm"
include "simpl1.mm"
include "simpr.mm"
include "sseldd.mm"
include "elpwid.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "sylanbrc.mm"
include "simpl3.mm"
include "notbid.mm"
include "rspcva.mm"
include "simplrl.mm"
include "ssel2.mm"
include "adantlr.mm"
include "3adantl3.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "3exp.mm"
include "syl5bi.mm"
include "rexlimdv.mm"

theorem fin23lem11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vy: setvar y
  let cV: class V
  assume fin23lem11.1: |- ( z = ( A \ x ) -> ( ps <-> ch ) )
  assume fin23lem11.2: |- ( w = ( A \ v ) -> ( ph <-> th ) )
  assume fin23lem11.3: |- ( ( x C_ A /\ v C_ A ) -> ( ch <-> th ) )

  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c z
  disjoint A c
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B c
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B z
  disjoint ch z
  disjoint ph v
  disjoint ps x
  disjoint th w
  disjoint c y
  disjoint v y
  disjoint w y
  disjoint x y
  disjoint y z
  disjoint A y
  disjoint B y
  disjoint V y
  assert |- ( B C_ ~P A -> ( E. x e. { c e. ~P A | ( A \ c ) e. B } A. w e. { c e. ~P A | ( A \ c ) e. B } -. ph -> E. z e. B A. v e. B -. ps ) )

  proof
    cB
    cA
    cpw
    #
    wss
    #
    wph
    wn
    #
    vw
    cA
    vc
    cv
    #
    cdif
    #
    cB
    wcel
    #
    vc
    @0
    crab
    #
    wral
    #
    wps
    wn
    #
    vv
    cB
    wral
    #
    vz
    cB
    wrex
    #
    vx
    @6
    vx
    cv
    #
    @6
    wcel
    @11
    @0
    wcel
    #
    cA
    @11
    cdif
    #
    cB
    wcel
    #
    wa
    #
    @1
    @7
    @10
    wi
    @5
    @14
    vc
    @11
    @0
    @3
    @11
    wceq
    @4
    @13
    cB
    @3
    @11
    cA
    difeq2
    eleq1d
    elrab
    @1
    @15
    @7
    @10
    @1
    @15
    @7
    w3a
    #
    @14
    wch
    wn
    #
    vv
    cB
    wral
    #
    @10
    @1
    @12
    @14
    @7
    simp2r
    @16
    @17
    vv
    cB
    @16
    vv
    cv
    #
    cB
    wcel
    #
    wa
    #
    @17
    wth
    wn
    #
    @21
    cA
    @19
    cdif
    #
    @6
    wcel
    #
    @7
    @22
    @21
    @23
    @0
    wcel
    #
    cA
    @23
    cdif
    #
    cB
    wcel
    #
    @24
    @21
    @25
    @23
    cA
    wss
    #
    cA
    @19
    difss
    @21
    cA
    cvv
    wcel
    #
    @25
    @28
    wb
    @21
    cA
    @13
    @11
    cun
    #
    wss
    @30
    cvv
    wcel
    #
    @29
    cA
    cA
    @11
    cun
    @30
    cA
    @11
    ssun1
    cA
    @11
    undif1
    sseqtr4i
    @21
    @14
    @12
    @31
    @12
    @14
    @1
    @7
    @20
    simpl2r
    @12
    @14
    @1
    @7
    @20
    simpl2l
    @13
    @11
    cB
    @0
    unexg
    syl2anc
    cA
    @30
    cvv
    ssexg
    sylancr
    @23
    cA
    cvv
    elpw2g
    syl
    mpbiri
    @21
    @26
    @19
    cB
    @21
    @19
    cA
    wss
    #
    @26
    @19
    wceq
    @21
    @19
    cA
    @21
    cB
    @0
    @19
    @1
    @15
    @7
    @20
    simpl1
    @16
    @20
    simpr
    #
    sseldd
    elpwid
    @19
    cA
    dfss4
    sylib
    @33
    eqeltrd
    @5
    @27
    vc
    @23
    @0
    @3
    @23
    wceq
    @4
    @26
    cB
    @3
    @23
    cA
    difeq2
    eleq1d
    elrab
    sylanbrc
    @1
    @15
    @7
    @20
    simpl3
    @2
    @22
    vw
    @23
    @6
    vw
    cv
    @23
    wceq
    wph
    wth
    fin23lem11.2
    notbid
    rspcva
    syl2anc
    @1
    @15
    @20
    @17
    @22
    wb
    @7
    @1
    @15
    wa
    @20
    wa
    #
    wch
    wth
    @34
    @11
    cA
    wss
    @32
    wch
    wth
    wb
    @34
    @11
    cA
    @1
    @12
    @14
    @20
    simplrl
    elpwid
    @34
    @19
    cA
    @1
    @20
    @19
    @0
    wcel
    @15
    cB
    @0
    @19
    ssel2
    adantlr
    elpwid
    fin23lem11.3
    syl2anc
    notbid
    3adantl3
    mpbird
    ralrimiva
    @9
    @18
    vz
    @13
    cB
    vz
    cv
    @13
    wceq
    #
    @8
    @17
    vv
    cB
    @35
    wps
    wch
    fin23lem11.1
    notbid
    ralbidv
    rspcev
    syl2anc
    3exp
    syl5bi
    rexlimdv
end
