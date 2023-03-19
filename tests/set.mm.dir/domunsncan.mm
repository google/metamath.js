include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "cdom.mm"
include "wbr.mm"
include "cvv.mm"
include "wss.mm"
include "ssun2.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "adantl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "brdomi.mm"
include "cdif.mm"
include "cima.mm"
include "cen.mm"
include "cres.mm"
include "wf1o.mm"
include "vex.mm"
include "resex.mm"
include "simprr.mm"
include "difss.mm"
include "f1ores.mm"
include "sylancl.mm"
include "f1oen3g.mm"
include "wceq.mm"
include "ccnv.mm"
include "wfun.mm"
include "wf.mm"
include "df-f1.mm"
include "simprbi.mm"
include "imadif.mm"
include "syl.mm"
include "ad2antll.mm"
include "cfv.mm"
include "snex.mm"
include "simprl.mm"
include "unexg.mm"
include "difexg.mm"
include "f1f.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "ssdifd.mm"
include "wfn.mm"
include "f1fn.mm"
include "snid.mm"
include "elun1.mm"
include "ax-mp.mm"
include "fnsnfv.mm"
include "difeq2d.mm"
include "sseqtr4d.mm"
include "ssdomg.mm"
include "sylc.mm"
include "ffvelrn.mm"
include "mp1i.mm"
include "difsnen.mm"
include "syl3anc.mm"
include "domentr.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "endomtr.mm"
include "uncom.mm"
include "difeq1i.mm"
include "difun2.mm"
include "eqtri.mm"
include "difsn.mm"
include "syl5eq.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "3brtr3d.mm"
include "expr.mm"
include "exlimdv.mm"
include "syl5.mm"
include "impancom.mm"
include "mpd.mm"
include "cin.mm"
include "c0.mm"
include "en2sn.mm"
include "mp2an.mm"
include "endom.mm"
include "simpr.mm"
include "incom.mm"
include "disjsn.mm"
include "biimpri.mm"
include "undom.mm"
include "syl21anc.mm"
include "impbida.mm"

theorem domunsncan
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume domunsncan.a: |- A e. _V
  assume domunsncan.b: |- B e. _V


  assert |- ( ( -. A e. X /\ -. B e. Y ) -> ( ( { A } u. X ) ~<_ ( { B } u. Y ) <-> X ~<_ Y ) )

  proof
    cA
    cX
    wcel
    wn
    #
    cB
    cY
    wcel
    wn
    #
    wa
    #
    cA
    csn
    #
    cX
    cun
    #
    cB
    csn
    #
    cY
    cun
    #
    cdom
    wbr
    #
    cX
    cY
    cdom
    wbr
    #
    @2
    @7
    wa
    #
    cY
    cvv
    wcel
    #
    @8
    @9
    cY
    @6
    wss
    @6
    cvv
    wcel
    #
    @10
    cY
    @5
    ssun2
    @7
    @11
    @2
    @4
    @6
    cdom
    reldom
    brrelex2i
    adantl
    cY
    @6
    cvv
    ssexg
    sylancr
    @2
    @10
    @7
    @8
    @7
    @4
    @6
    vf
    cv
    #
    wf1
    #
    vf
    wex
    @2
    @10
    wa
    #
    @8
    @4
    @6
    vf
    brdomi
    @14
    @13
    @8
    vf
    @2
    @10
    @13
    @8
    @2
    @10
    @13
    wa
    #
    wa
    #
    @4
    @3
    cdif
    #
    @6
    @5
    cdif
    #
    cX
    cY
    cdom
    @16
    @17
    @12
    @17
    cima
    #
    cen
    wbr
    #
    @19
    @18
    cdom
    wbr
    @17
    @18
    cdom
    wbr
    @16
    @12
    @17
    cres
    #
    cvv
    wcel
    @17
    @19
    @21
    wf1o
    #
    @20
    @12
    @17
    vf
    vex
    resex
    @16
    @13
    @17
    @4
    wss
    @22
    @2
    @10
    @13
    simprr
    @4
    @3
    difss
    @4
    @6
    @17
    @12
    f1ores
    sylancl
    @17
    @19
    @21
    cvv
    f1oen3g
    sylancr
    @16
    @19
    @12
    @4
    cima
    #
    @12
    @3
    cima
    #
    cdif
    #
    @18
    cdom
    @13
    @19
    @25
    wceq
    #
    @2
    @10
    @13
    @12
    ccnv
    wfun
    #
    @26
    @13
    @4
    @6
    @12
    wf
    #
    @27
    @4
    @6
    @12
    df-f1
    simprbi
    @4
    @3
    @12
    imadif
    syl
    ad2antll
    @16
    @25
    @6
    cA
    @12
    cfv
    #
    csn
    #
    cdif
    #
    cdom
    wbr
    #
    @31
    @18
    cen
    wbr
    #
    @25
    @18
    cdom
    wbr
    @16
    @31
    cvv
    wcel
    #
    @25
    @31
    wss
    @32
    @16
    @11
    @34
    @16
    @5
    cvv
    wcel
    @10
    @11
    cB
    snex
    @2
    @10
    @13
    simprl
    @5
    cY
    cvv
    cvv
    unexg
    sylancr
    #
    @6
    @30
    cvv
    difexg
    syl
    @16
    @25
    @6
    @24
    cdif
    @31
    @16
    @23
    @6
    @24
    @13
    @23
    @6
    wss
    #
    @2
    @10
    @13
    @28
    @36
    @4
    @6
    @12
    f1f
    #
    @28
    @23
    @12
    crn
    @6
    @12
    @4
    imassrn
    @4
    @6
    @12
    frn
    syl5ss
    syl
    ad2antll
    ssdifd
    @16
    @30
    @24
    @6
    @16
    @12
    @4
    wfn
    #
    cA
    @4
    wcel
    #
    @30
    @24
    wceq
    @13
    @38
    @2
    @10
    @4
    @6
    @12
    f1fn
    ad2antll
    cA
    @3
    wcel
    @39
    cA
    domunsncan.a
    snid
    cA
    @3
    cX
    elun1
    ax-mp
    #
    @4
    cA
    @12
    fnsnfv
    sylancl
    difeq2d
    sseqtr4d
    @25
    @31
    cvv
    ssdomg
    sylc
    @16
    @11
    @29
    @6
    wcel
    #
    cB
    @6
    wcel
    #
    @33
    @35
    @13
    @41
    @2
    @10
    @13
    @28
    @39
    @41
    @37
    @40
    @4
    @6
    cA
    @12
    ffvelrn
    sylancl
    ad2antll
    cB
    @5
    wcel
    @42
    @16
    cB
    domunsncan.b
    snid
    cB
    @5
    cY
    elun1
    mp1i
    @29
    cB
    cvv
    @6
    difsnen
    syl3anc
    @25
    @31
    @18
    domentr
    syl2anc
    eqbrtrd
    @17
    @19
    @18
    endomtr
    syl2anc
    @0
    @17
    cX
    wceq
    @1
    @15
    @0
    @17
    cX
    @3
    cdif
    #
    cX
    @17
    cX
    @3
    cun
    #
    @3
    cdif
    @43
    @4
    @44
    @3
    @3
    cX
    uncom
    difeq1i
    cX
    @3
    difun2
    eqtri
    cA
    cX
    difsn
    syl5eq
    ad2antrr
    @1
    @18
    cY
    wceq
    @0
    @15
    @1
    @18
    cY
    @5
    cdif
    #
    cY
    @18
    cY
    @5
    cun
    #
    @5
    cdif
    @45
    @6
    @46
    @5
    @5
    cY
    uncom
    difeq1i
    cY
    @5
    difun2
    eqtri
    cB
    cY
    difsn
    syl5eq
    ad2antlr
    3brtr3d
    expr
    exlimdv
    syl5
    impancom
    mpd
    @2
    @8
    wa
    #
    @3
    @5
    cdom
    wbr
    #
    @8
    @5
    cY
    cin
    #
    c0
    wceq
    #
    @7
    @3
    @5
    cen
    wbr
    #
    @48
    @47
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    @51
    domunsncan.a
    domunsncan.b
    cA
    cB
    cvv
    cvv
    en2sn
    mp2an
    @3
    @5
    endom
    mp1i
    @2
    @8
    simpr
    @1
    @50
    @0
    @8
    @1
    @49
    cY
    @5
    cin
    #
    c0
    @5
    cY
    incom
    @52
    c0
    wceq
    @1
    cY
    cB
    disjsn
    biimpri
    syl5eq
    ad2antlr
    @3
    @5
    cX
    cY
    undom
    syl21anc
    impbida
end
