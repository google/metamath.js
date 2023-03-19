include "con0.mm"
include "wcel.mm"
include "ccf.mm"
include "cfv.mm"
include "cv.mm"
include "ccrd.mm"
include "wceq.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wf1.mm"
include "cab.mm"
include "cint.mm"
include "cfval.mm"
include "c0.mm"
include "wne.mm"
include "cardon.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantr.mm"
include "exlimiv.mm"
include "abssi.mm"
include "cflem.mm"
include "abn0.mm"
include "sylibr.mm"
include "onint.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "fvex.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "elab.mm"
include "sylib.mm"
include "wf1o.mm"
include "simplr.mm"
include "onss.mm"
include "sstr.mm"
include "sylan2.mm"
include "ancoms.mm"
include "ad2ant2r.mm"
include "cen.mm"
include "wbr.mm"
include "cdm.mm"
include "cvv.mm"
include "vex.mm"
include "onssnum.mm"
include "mpan.mm"
include "cardid2.mm"
include "syl.mm"
include "adantl.mm"
include "wb.mm"
include "breq1.mm"
include "mpbird.mm"
include "bren.mm"
include "syl2anc.mm"
include "w3a.mm"
include "f1of1.mm"
include "f1ss.mm"
include "adantlr.mm"
include "3adant1.mm"
include "wfo.mm"
include "wi.mm"
include "f1ofo.mm"
include "foelrn.mm"
include "sseq2.mm"
include "biimpcd.mm"
include "reximdv.mm"
include "syl5com.mm"
include "rexlimdva.mm"
include "ralimdv.mm"
include "impcom.mm"
include "adantll.mm"
include "jca.mm"
include "3expia.mm"
include "eximdv.mm"
include "mpd.mm"
include "expl.mm"
include "exlimdv.mm"

theorem cff1
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vf: setvar f
  let vs: setvar s
  let vy: setvar y
  let vx: setvar x

  disjoint A f
  disjoint A w
  disjoint A z
  disjoint f w
  disjoint f z
  disjoint w z
  disjoint A s
  disjoint A y
  disjoint f s
  disjoint f y
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint w y
  disjoint y z
  disjoint A x
  disjoint s x
  disjoint x y
  disjoint x z
  assert |- ( A e. On -> E. f ( f : ( cf ` A ) -1-1-> A /\ A. z e. A E. w e. ( cf ` A ) z C_ ( f ` w ) ) )

  proof
    cA
    con0
    wcel
    #
    cA
    ccf
    cfv
    #
    vy
    cv
    #
    ccrd
    cfv
    #
    wceq
    #
    @2
    cA
    wss
    #
    vz
    cv
    #
    vs
    cv
    #
    wss
    #
    vs
    @2
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    @1
    cA
    vf
    cv
    #
    wf1
    #
    @6
    vw
    cv
    @14
    cfv
    #
    wss
    #
    vw
    @1
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    @0
    @1
    vx
    cv
    #
    @3
    wceq
    #
    @11
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    wcel
    @13
    @0
    @1
    @26
    cint
    #
    @26
    vx
    vy
    vz
    vs
    cA
    cfval
    @0
    @26
    con0
    wss
    @26
    c0
    wne
    #
    @27
    @26
    wcel
    @25
    vx
    con0
    @24
    @22
    con0
    wcel
    #
    vy
    @23
    @29
    @11
    @23
    @29
    @3
    con0
    wcel
    @2
    cardon
    @22
    @3
    con0
    eleq1
    mpbiri
    adantr
    exlimiv
    abssi
    @0
    @25
    vx
    wex
    @28
    vx
    vy
    vz
    vs
    cA
    con0
    cflem
    @25
    vx
    abn0
    sylibr
    @26
    onint
    sylancr
    eqeltrd
    @25
    @13
    vx
    @1
    cA
    ccf
    fvex
    @22
    @1
    wceq
    #
    @24
    @12
    vy
    @30
    @23
    @4
    @11
    @22
    @1
    @3
    eqeq1
    anbi1d
    exbidv
    elab
    sylib
    @0
    @12
    @21
    vy
    @0
    @4
    @11
    @21
    @0
    @4
    wa
    #
    @11
    wa
    #
    @1
    @2
    @14
    wf1o
    #
    vf
    wex
    #
    @21
    @32
    @4
    @2
    con0
    wss
    #
    @34
    @0
    @4
    @11
    simplr
    @0
    @5
    @35
    @4
    @10
    @5
    @0
    @35
    @0
    @5
    cA
    con0
    wss
    @35
    cA
    onss
    @2
    cA
    con0
    sstr
    sylan2
    ancoms
    ad2ant2r
    @4
    @35
    wa
    #
    @1
    @2
    cen
    wbr
    #
    @34
    @36
    @37
    @3
    @2
    cen
    wbr
    #
    @35
    @38
    @4
    @35
    @2
    ccrd
    cdm
    wcel
    #
    @38
    @2
    cvv
    wcel
    @35
    @39
    vy
    vex
    @2
    cvv
    onssnum
    mpan
    @2
    cardid2
    syl
    adantl
    @4
    @37
    @38
    wb
    @35
    @1
    @3
    @2
    cen
    breq1
    adantr
    mpbird
    @1
    @2
    vf
    bren
    sylib
    syl2anc
    @32
    @33
    @20
    vf
    @31
    @11
    @33
    @20
    @31
    @11
    @33
    w3a
    @15
    @19
    @11
    @33
    @15
    @31
    @5
    @33
    @15
    @10
    @33
    @5
    @1
    @2
    @14
    wf1
    #
    @15
    @1
    @2
    @14
    f1of1
    @40
    @5
    @15
    @1
    @2
    cA
    @14
    f1ss
    ancoms
    sylan2
    adantlr
    3adant1
    @11
    @33
    @19
    @31
    @10
    @33
    @19
    @5
    @33
    @10
    @19
    @33
    @1
    @2
    @14
    wfo
    #
    @10
    @19
    wi
    @1
    @2
    @14
    f1ofo
    @41
    @9
    @18
    vz
    cA
    @41
    @8
    @18
    vs
    @2
    @41
    @7
    @2
    wcel
    wa
    @7
    @16
    wceq
    #
    vw
    @1
    wrex
    @8
    @18
    vw
    @1
    @2
    @7
    @14
    foelrn
    @8
    @42
    @17
    vw
    @1
    @42
    @8
    @17
    @7
    @16
    @6
    sseq2
    biimpcd
    reximdv
    syl5com
    rexlimdva
    ralimdv
    syl
    impcom
    adantll
    3adant1
    jca
    3expia
    eximdv
    mpd
    expl
    exlimdv
    mpd
end
