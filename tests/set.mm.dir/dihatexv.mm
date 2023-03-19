include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cdif.mm"
include "cple.mm"
include "wbr.mm"
include "cid.mm"
include "cres.mm"
include "cltrn.mm"
include "cmpt.mm"
include "cop.mm"
include "chlt.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "eqid.mm"
include "dih1dimb2.mm"
include "syl12anc.mm"
include "ctendo.mm"
include "ad3antrrr.mm"
include "tendo0cl.mm"
include "syl.mm"
include "dvhelvbasei.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylan.mm"
include "ex.mm"
include "adantld.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "wn.mm"
include "coc.mm"
include "crio.mm"
include "lhpocnel2.mm"
include "ltrniotacl.mm"
include "syl112anc.mm"
include "tendoidcl.mm"
include "dih1dimc.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "cp0.mm"
include "cal.mm"
include "simpld.mm"
include "hlatl.mm"
include "simpllr.mm"
include "atn0.mm"
include "w3a.mm"
include "3ad2ant3.mm"
include "clmod.mm"
include "simp1ll.mm"
include "dvhlmod.mm"
include "lspsn0.mm"
include "3syl.mm"
include "eqtrd.mm"
include "simp2.mm"
include "dih0.mm"
include "3eqtr4d.mm"
include "wb.mm"
include "cops.mm"
include "hlop.mm"
include "op0cl.mm"
include "dih11.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "3expia.mm"
include "necon3d.mm"
include "ancrd.mm"
include "reximdva.mm"
include "ccnv.mm"
include "dihcnvid1.mm"
include "fveq2.mm"
include "ad2antll.mm"
include "eqtr3d.mm"
include "clsa.mm"
include "simprl.mm"
include "lsatlspsn2.mm"
include "dihlatat.mm"
include "eqeltrd.mm"
include "impbid.mm"
include "rexdifsn.mm"
include "syl6bbr.mm"

theorem dihatexv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vf: setvar f
  let vg: setvar g
  assume dihatexv.b: |- B = ( Base ` K )
  assume dihatexv.a: |- A = ( Atoms ` K )
  assume dihatexv.h: |- H = ( LHyp ` K )
  assume dihatexv.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihatexv.v: |- V = ( Base ` U )
  assume dihatexv.o: |- .0. = ( 0g ` U )
  assume dihatexv.n: |- N = ( LSpan ` U )
  assume dihatexv.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihatexv.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihatexv.q: |- ( ph -> Q e. B )

  disjoint A x
  disjoint B x
  disjoint I x
  disjoint K x
  disjoint N x
  disjoint Q x
  disjoint V x
  disjoint W x
  disjoint ph x
  disjoint f x
  disjoint g x
  disjoint f g
  disjoint A f
  disjoint A g
  disjoint B f
  disjoint H f
  disjoint H g
  disjoint I g
  disjoint K f
  disjoint K g
  disjoint N g
  disjoint Q f
  disjoint Q g
  disjoint V g
  disjoint W f
  disjoint W g
  disjoint g ph
  assert |- ( ph -> ( Q e. A <-> E. x e. ( V \ { .0. } ) ( I ` Q ) = ( N ` { x } ) ) )

  proof
    wph
    cQ
    cA
    wcel
    #
    vx
    cv
    #
    c.0
    wne
    #
    cQ
    cI
    cfv
    #
    @1
    csn
    #
    cN
    cfv
    #
    wceq
    #
    wa
    #
    vx
    cV
    wrex
    #
    @6
    vx
    cV
    c.0
    csn
    #
    cdif
    wrex
    wph
    @0
    @8
    wph
    @0
    @8
    wph
    @0
    wa
    #
    @6
    vx
    cV
    wrex
    #
    @8
    @10
    cQ
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @11
    @10
    @13
    wa
    #
    vg
    cv
    #
    cid
    cB
    cres
    #
    wne
    #
    @3
    @15
    vf
    cW
    cK
    cltrn
    cfv
    cfv
    #
    @16
    cmpt
    #
    cop
    #
    csn
    #
    cN
    cfv
    #
    wceq
    #
    wa
    #
    vg
    @18
    wrex
    #
    @11
    @14
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    @0
    @13
    @25
    wph
    @28
    @0
    @13
    dihatexv.k
    ad2antrr
    wph
    @0
    @13
    simplr
    @10
    @13
    simpr
    cA
    cB
    cQ
    @18
    cU
    vg
    vf
    cH
    cI
    cK
    @12
    cN
    @19
    cW
    dihatexv.b
    @12
    eqid
    #
    dihatexv.a
    dihatexv.h
    @18
    eqid
    #
    @19
    eqid
    #
    dihatexv.u
    dihatexv.i
    dihatexv.n
    dih1dimb2
    syl12anc
    @14
    @24
    @11
    vg
    @18
    @14
    @15
    @18
    wcel
    #
    wa
    #
    @23
    @11
    @17
    @33
    @23
    @11
    @33
    @20
    cV
    wcel
    #
    @23
    @11
    @33
    @28
    @32
    @19
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    #
    @34
    wph
    @28
    @0
    @13
    @32
    dihatexv.k
    ad3antrrr
    #
    @14
    @32
    simpr
    @33
    @28
    @36
    @37
    cB
    @18
    vf
    @35
    cH
    cK
    @19
    cW
    dihatexv.b
    dihatexv.h
    @30
    @35
    eqid
    #
    @31
    tendo0cl
    syl
    @19
    @18
    cU
    @35
    @15
    cH
    cK
    cV
    cW
    chlt
    dihatexv.h
    @30
    @38
    dihatexv.u
    dihatexv.v
    dvhelvbasei
    syl12anc
    @6
    @23
    vx
    @20
    cV
    @1
    @20
    wceq
    #
    @5
    @22
    @3
    @39
    @4
    @21
    cN
    @1
    @20
    sneq
    fveq2d
    eqeq2d
    rspcev
    sylan
    ex
    adantld
    rexlimdva
    mpd
    @10
    @13
    wn
    #
    wa
    #
    cW
    cK
    coc
    cfv
    cfv
    #
    vf
    cv
    cfv
    cQ
    wceq
    vf
    @18
    crio
    #
    cid
    @18
    cres
    #
    cop
    #
    cV
    wcel
    #
    @3
    @45
    csn
    #
    cN
    cfv
    #
    wceq
    #
    @11
    @41
    @28
    @43
    @18
    wcel
    #
    @44
    @35
    wcel
    #
    @46
    wph
    @28
    @0
    @40
    dihatexv.k
    ad2antrr
    #
    @41
    @28
    @42
    cA
    wcel
    @42
    cW
    @12
    wbr
    wn
    wa
    #
    @0
    @40
    @50
    @52
    @41
    @28
    @53
    @52
    cA
    @42
    cH
    cK
    @12
    cW
    @29
    dihatexv.a
    dihatexv.h
    @42
    eqid
    #
    lhpocnel2
    syl
    wph
    @0
    @40
    simplr
    #
    @10
    @40
    simpr
    #
    cA
    @42
    cQ
    @18
    vf
    @43
    cH
    cK
    @12
    cW
    @29
    dihatexv.a
    dihatexv.h
    @30
    @43
    eqid
    #
    ltrniotacl
    syl112anc
    @41
    @28
    @51
    @52
    @18
    @35
    cH
    cK
    cW
    dihatexv.h
    @30
    @38
    tendoidcl
    syl
    @44
    @18
    cU
    @35
    @43
    cH
    cK
    cV
    cW
    chlt
    dihatexv.h
    @30
    @38
    dihatexv.u
    dihatexv.v
    dvhelvbasei
    syl12anc
    @41
    @28
    @0
    @40
    @49
    @52
    @55
    @56
    cA
    @42
    cQ
    @18
    cU
    vf
    @43
    cH
    cI
    cK
    @12
    cN
    cW
    @29
    dihatexv.a
    dihatexv.h
    @54
    @30
    dihatexv.i
    dihatexv.u
    dihatexv.n
    @57
    dih1dimc
    syl12anc
    @6
    @49
    vx
    @45
    cV
    @1
    @45
    wceq
    #
    @5
    @48
    @3
    @58
    @4
    @47
    cN
    @1
    @45
    sneq
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    pm2.61dan
    @10
    @6
    @7
    vx
    cV
    @10
    @1
    cV
    wcel
    #
    wa
    #
    @6
    @2
    @60
    @6
    @2
    @60
    @6
    wa
    #
    cQ
    cK
    cp0
    cfv
    #
    wne
    #
    @2
    @61
    cK
    cal
    wcel
    #
    @0
    @63
    @61
    @26
    @64
    wph
    @26
    @0
    @59
    @6
    wph
    @26
    @27
    dihatexv.k
    simpld
    #
    ad3antrrr
    cK
    hlatl
    syl
    wph
    @0
    @59
    @6
    simpllr
    cA
    cQ
    cK
    @62
    @62
    eqid
    #
    dihatexv.a
    atn0
    syl2anc
    @61
    @1
    c.0
    cQ
    @62
    @60
    @6
    @1
    c.0
    wceq
    #
    cQ
    @62
    wceq
    #
    @60
    @6
    @67
    w3a
    #
    @3
    @62
    cI
    cfv
    #
    wceq
    #
    @68
    @69
    @5
    @9
    @3
    @70
    @69
    @5
    @9
    cN
    cfv
    #
    @9
    @67
    @60
    @5
    @72
    wceq
    @6
    @67
    @4
    @9
    cN
    @1
    c.0
    sneq
    fveq2d
    3ad2ant3
    @69
    wph
    cU
    clmod
    wcel
    #
    @72
    @9
    wceq
    wph
    @0
    @59
    @6
    @67
    simp1ll
    #
    wph
    cU
    cH
    cK
    cW
    dihatexv.h
    dihatexv.u
    dihatexv.k
    dvhlmod
    #
    cN
    cU
    c.0
    dihatexv.o
    dihatexv.n
    lspsn0
    3syl
    eqtrd
    @60
    @6
    @67
    simp2
    @69
    wph
    @28
    @70
    @9
    wceq
    @74
    dihatexv.k
    cU
    cH
    cI
    cK
    c.0
    cW
    @62
    @66
    dihatexv.h
    dihatexv.i
    dihatexv.u
    dihatexv.o
    dih0
    3syl
    3eqtr4d
    @69
    @28
    cQ
    cB
    wcel
    #
    @62
    cB
    wcel
    #
    @71
    @68
    wb
    @69
    wph
    @28
    @74
    dihatexv.k
    syl
    @69
    wph
    @76
    @74
    dihatexv.q
    syl
    @69
    @26
    cK
    cops
    wcel
    @77
    @69
    wph
    @26
    @74
    @65
    syl
    cK
    hlop
    cB
    cK
    @62
    dihatexv.b
    @66
    op0cl
    3syl
    cB
    cH
    cI
    cK
    cW
    cQ
    @62
    dihatexv.b
    dihatexv.h
    dihatexv.i
    dih11
    syl3anc
    mpbid
    3expia
    necon3d
    mpd
    ex
    ancrd
    reximdva
    mpd
    ex
    wph
    @7
    @0
    vx
    cV
    wph
    @59
    wa
    #
    @7
    @0
    @78
    @7
    wa
    #
    cQ
    @5
    cI
    ccnv
    #
    cfv
    #
    cA
    @79
    @3
    @80
    cfv
    #
    cQ
    @81
    @79
    @28
    @76
    @82
    cQ
    wceq
    wph
    @28
    @59
    @7
    dihatexv.k
    ad2antrr
    #
    wph
    @76
    @59
    @7
    dihatexv.q
    ad2antrr
    cB
    cH
    cI
    cK
    cW
    cQ
    dihatexv.b
    dihatexv.h
    dihatexv.i
    dihcnvid1
    syl2anc
    @6
    @82
    @81
    wceq
    @78
    @2
    @3
    @5
    @80
    fveq2
    ad2antll
    eqtr3d
    @79
    @28
    @5
    cU
    clsa
    cfv
    #
    wcel
    #
    @81
    cA
    wcel
    @83
    @79
    @73
    @59
    @2
    @85
    wph
    @73
    @59
    @7
    @75
    ad2antrr
    wph
    @59
    @7
    simplr
    @78
    @2
    @6
    simprl
    @84
    cN
    cV
    cU
    @1
    c.0
    dihatexv.v
    dihatexv.n
    dihatexv.o
    @84
    eqid
    #
    lsatlspsn2
    syl3anc
    cA
    @5
    cU
    cH
    cI
    cK
    @84
    cW
    dihatexv.a
    dihatexv.h
    dihatexv.u
    dihatexv.i
    @86
    dihlatat
    syl2anc
    eqeltrd
    ex
    rexlimdva
    impbid
    @6
    vx
    cV
    c.0
    rexdifsn
    syl6bbr
end
