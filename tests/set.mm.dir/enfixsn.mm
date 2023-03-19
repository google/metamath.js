include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "wf1o.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "simp3.mm"
include "bren.mm"
include "sylib.mm"
include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "relen.mm"
include "brrelex2i.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "wf.mm"
include "f1of.mm"
include "adantl.mm"
include "simpl1.mm"
include "ffvelrnd.mm"
include "simpl2.mm"
include "difsnen.mm"
include "syl3anc.mm"
include "cop.mm"
include "cun.mm"
include "ccom.mm"
include "cin.mm"
include "c0.mm"
include "fvex.mm"
include "a1i.mm"
include "f1osng.mm"
include "syl2anc.mm"
include "simprr.mm"
include "disjdif.mm"
include "f1oun.mm"
include "syl22anc.mm"
include "wb.mm"
include "ad2antrl.mm"
include "uncom.mm"
include "difsnid.mm"
include "syl5eq.mm"
include "syl.mm"
include "f1oeq23.mm"
include "mpbid.mm"
include "simprl.mm"
include "f1oco.mm"
include "wfn.mm"
include "f1ofn.mm"
include "fvco2.mm"
include "ad2antll.mm"
include "snid.mm"
include "fvun1.mm"
include "syl112anc.mm"
include "fvsng.mm"
include "3eqtrd.mm"
include "snex.mm"
include "vex.mm"
include "unex.mm"
include "coex.mm"
include "f1oeq1.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "spcev.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "exlimddv.mm"

theorem enfixsn
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vh: setvar h

  disjoint A f
  disjoint B f
  disjoint X f
  disjoint Y f
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B g
  disjoint B h
  disjoint X g
  disjoint X h
  disjoint Y g
  disjoint Y h
  assert |- ( ( A e. X /\ B e. Y /\ X ~~ Y ) -> E. f ( f : X -1-1-onto-> Y /\ ( f ` A ) = B ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cX
    cY
    cen
    wbr
    #
    w3a
    #
    cX
    cY
    vg
    cv
    #
    wf1o
    #
    cX
    cY
    vf
    cv
    #
    wf1o
    #
    cA
    @6
    cfv
    #
    cB
    wceq
    #
    wa
    #
    vf
    wex
    #
    vg
    @3
    @2
    @5
    vg
    wex
    @0
    @1
    @2
    simp3
    cX
    cY
    vg
    bren
    sylib
    @3
    @5
    wa
    #
    cY
    cA
    @4
    cfv
    #
    csn
    #
    cdif
    #
    cY
    cB
    csn
    #
    cdif
    #
    vh
    cv
    #
    wf1o
    #
    vh
    wex
    #
    @11
    @12
    @15
    @17
    cen
    wbr
    #
    @20
    @12
    cY
    cvv
    wcel
    #
    @13
    cY
    wcel
    #
    @1
    @21
    @3
    @22
    @5
    @2
    @0
    @22
    @1
    cX
    cY
    cen
    relen
    brrelex2i
    3ad2ant3
    adantr
    @12
    cX
    cY
    cA
    @4
    @5
    cX
    cY
    @4
    wf
    #
    @3
    cX
    cY
    @4
    f1of
    #
    adantl
    @0
    @1
    @2
    @5
    simpl1
    ffvelrnd
    @0
    @1
    @2
    @5
    simpl2
    @13
    cB
    cvv
    cY
    difsnen
    syl3anc
    @15
    @17
    vh
    bren
    sylib
    @12
    @19
    @11
    vh
    @3
    @5
    @19
    @11
    @3
    @5
    @19
    wa
    #
    wa
    #
    cX
    cY
    @13
    cB
    cop
    #
    csn
    #
    @18
    cun
    #
    @4
    ccom
    #
    wf1o
    #
    cA
    @31
    cfv
    #
    cB
    wceq
    #
    @11
    @27
    cY
    cY
    @30
    wf1o
    #
    @5
    @32
    @27
    @14
    @15
    cun
    #
    @16
    @17
    cun
    #
    @30
    wf1o
    #
    @35
    @27
    @14
    @16
    @29
    wf1o
    #
    @19
    @14
    @15
    cin
    c0
    wceq
    #
    @16
    @17
    cin
    c0
    wceq
    #
    @38
    @27
    @13
    cvv
    wcel
    #
    @1
    @39
    @42
    @27
    cA
    @4
    fvex
    #
    a1i
    #
    @0
    @1
    @2
    @26
    simpl2
    #
    @13
    cB
    cvv
    cY
    f1osng
    syl2anc
    #
    @3
    @5
    @19
    simprr
    @40
    @27
    @14
    cY
    disjdif
    a1i
    #
    @41
    @27
    @16
    cY
    disjdif
    a1i
    @14
    @16
    @15
    @17
    @29
    @18
    f1oun
    syl22anc
    @27
    @36
    cY
    wceq
    #
    @37
    cY
    wceq
    #
    @38
    @35
    wb
    @27
    @23
    @48
    @27
    cX
    cY
    cA
    @4
    @5
    @24
    @3
    @19
    @25
    ad2antrl
    @0
    @1
    @2
    @26
    simpl1
    #
    ffvelrnd
    @23
    @36
    @15
    @14
    cun
    cY
    @14
    @15
    uncom
    cY
    @13
    difsnid
    syl5eq
    syl
    @27
    @1
    @49
    @45
    @1
    @37
    @17
    @16
    cun
    cY
    @16
    @17
    uncom
    cY
    cB
    difsnid
    syl5eq
    syl
    @36
    cY
    @37
    cY
    @30
    f1oeq23
    syl2anc
    mpbid
    @3
    @5
    @19
    simprl
    cX
    cY
    cY
    @30
    @4
    f1oco
    syl2anc
    @27
    @33
    @13
    @30
    cfv
    #
    @13
    @29
    cfv
    #
    cB
    @27
    @4
    cX
    wfn
    #
    @0
    @33
    @51
    wceq
    @5
    @53
    @3
    @19
    cX
    cY
    @4
    f1ofn
    ad2antrl
    @50
    cX
    @30
    @4
    cA
    fvco2
    syl2anc
    @27
    @29
    @14
    wfn
    #
    @18
    @15
    wfn
    #
    @40
    @13
    @14
    wcel
    #
    @51
    @52
    wceq
    @27
    @39
    @54
    @46
    @14
    @16
    @29
    f1ofn
    syl
    @19
    @55
    @3
    @5
    @15
    @17
    @18
    f1ofn
    ad2antll
    @47
    @56
    @27
    @13
    @43
    snid
    a1i
    @14
    @15
    @29
    @18
    @13
    fvun1
    syl112anc
    @27
    @42
    @1
    @52
    cB
    wceq
    @44
    @45
    @13
    cB
    cvv
    cY
    fvsng
    syl2anc
    3eqtrd
    @10
    @32
    @34
    wa
    vf
    @31
    @30
    @4
    @29
    @18
    @28
    snex
    vh
    vex
    unex
    vg
    vex
    coex
    @6
    @31
    wceq
    #
    @7
    @32
    @9
    @34
    cX
    cY
    @6
    @31
    f1oeq1
    @57
    @8
    @33
    cB
    cA
    @6
    @31
    fveq1
    eqeq1d
    anbi12d
    spcev
    syl2anc
    expr
    exlimdv
    mpd
    exlimddv
end
