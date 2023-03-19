include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cnei.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "wral.mm"
include "wi.mm"
include "snssi.mm"
include "neiss.mm"
include "syl3an3.mm"
include "3exp.mm"
include "ralrimdv.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "wrex.mm"
include "wb.mm"
include "r19.28zv.mm"
include "3ad2ant3.mm"
include "crab.mm"
include "cuni.mm"
include "ssrab2.mm"
include "uniopn.mm"
include "mpan2.mm"
include "ad2antrr.mm"
include "sseq1.mm"
include "elrab.mm"
include "elunii.mm"
include "sylan2br.mm"
include "an12s.mm"
include "rexlimiva.mm"
include "ralimi.mm"
include "dfss3.mm"
include "sylibr.mm"
include "adantl.mm"
include "unissb.mm"
include "simprbi.mm"
include "mprgbir.mm"
include "jctir.mm"
include "wceq.mm"
include "sseq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "anim2d.mm"
include "3adant3.mm"
include "sylbid.mm"
include "ssel2.mm"
include "isneip.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "isnei.mm"
include "3imtr4d.mm"
include "impbid.mm"

theorem neips
  let cS: class S
  let cJ: class J
  let cN: class N
  let cX: class X
  let vp: setvar p
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let cM: class M
  let cP: class P
  assume neips.1: |- X = U. J

  disjoint J p
  disjoint N p
  disjoint S p
  disjoint X p
  disjoint g h
  disjoint g p
  disjoint g v
  disjoint J g
  disjoint h p
  disjoint h v
  disjoint J h
  disjoint p v
  disjoint J v
  disjoint M g
  disjoint N g
  disjoint N h
  disjoint N v
  disjoint P g
  disjoint S g
  disjoint S h
  disjoint X g
  disjoint X h
  assert |- ( ( J e. Top /\ S C_ X /\ S =/= (/) ) -> ( N e. ( ( nei ` J ) ` S ) <-> A. p e. S N e. ( ( nei ` J ) ` { p } ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cS
    c0
    wne
    #
    w3a
    #
    cN
    cS
    cJ
    cnei
    cfv
    #
    cfv
    wcel
    #
    cN
    vp
    cv
    #
    csn
    #
    @4
    cfv
    wcel
    #
    vp
    cS
    wral
    #
    @0
    @1
    @5
    @9
    wi
    @2
    @0
    @5
    @8
    vp
    cS
    @0
    @5
    @6
    cS
    wcel
    #
    @8
    @10
    @0
    @5
    @7
    cS
    wss
    @8
    @6
    cS
    snssi
    @7
    cS
    cJ
    cN
    neiss
    syl3an3
    3exp
    ralrimdv
    3ad2ant1
    @3
    cN
    cX
    wss
    #
    @6
    vg
    cv
    #
    wcel
    #
    @12
    cN
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    wa
    #
    vp
    cS
    wral
    #
    @11
    cS
    vh
    cv
    #
    wss
    #
    @19
    cN
    wss
    #
    wa
    #
    vh
    cJ
    wrex
    #
    wa
    #
    @9
    @5
    @3
    @18
    @11
    @16
    vp
    cS
    wral
    #
    wa
    #
    @24
    @2
    @0
    @18
    @26
    wb
    @1
    @11
    @16
    vp
    cS
    r19.28zv
    3ad2ant3
    @0
    @1
    @26
    @24
    wi
    @2
    @0
    @1
    wa
    #
    @25
    @23
    @11
    @27
    @25
    @23
    @27
    @25
    wa
    #
    vv
    cv
    #
    cN
    wss
    #
    vv
    cJ
    crab
    #
    cuni
    #
    cJ
    wcel
    #
    cS
    @32
    wss
    #
    @32
    cN
    wss
    #
    wa
    #
    @23
    @0
    @33
    @1
    @25
    @0
    @31
    cJ
    wss
    @33
    @30
    vv
    cJ
    ssrab2
    @31
    cJ
    uniopn
    mpan2
    ad2antrr
    @28
    @34
    @35
    @25
    @34
    @27
    @25
    @6
    @32
    wcel
    #
    vp
    cS
    wral
    @34
    @16
    @37
    vp
    cS
    @15
    @37
    vg
    cJ
    @13
    @12
    cJ
    wcel
    #
    @14
    @37
    @38
    @14
    wa
    @13
    @12
    @31
    wcel
    @37
    @30
    @14
    vv
    @12
    cJ
    @29
    @12
    cN
    sseq1
    elrab
    @6
    @12
    @31
    elunii
    sylan2br
    an12s
    rexlimiva
    ralimi
    vp
    cS
    @32
    dfss3
    sylibr
    adantl
    @35
    @21
    vh
    @31
    vh
    @31
    cN
    unissb
    @19
    @31
    wcel
    @19
    cJ
    wcel
    @21
    @30
    @21
    vv
    @19
    cJ
    @29
    @19
    cN
    sseq1
    elrab
    simprbi
    mprgbir
    jctir
    @22
    @36
    vh
    @32
    cJ
    @19
    @32
    wceq
    @20
    @34
    @21
    @35
    @19
    @32
    cS
    sseq2
    @19
    @32
    cN
    sseq1
    anbi12d
    rspcev
    syl2anc
    ex
    anim2d
    3adant3
    sylbid
    @0
    @1
    @9
    @18
    wb
    @2
    @27
    @8
    @17
    vp
    cS
    @0
    @1
    @10
    @8
    @17
    wb
    #
    @1
    @10
    wa
    @0
    @6
    cX
    wcel
    @39
    cS
    cX
    @6
    ssel2
    @6
    vg
    cJ
    cN
    cX
    neips.1
    isneip
    sylan2
    anassrs
    ralbidva
    3adant3
    @0
    @1
    @5
    @24
    wb
    @2
    cS
    vh
    cJ
    cN
    cX
    neips.1
    isnei
    3adant3
    3imtr4d
    impbid
end
