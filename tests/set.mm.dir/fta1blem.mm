include "csn.mm"
include "wcel.mm"
include "wceq.mm"
include "co.mm"
include "cfv.mm"
include "ccnv.mm"
include "cima.mm"
include "evl1vard.mm"
include "evl1vsd.mm"
include "simprd.mm"
include "eqtrd.mm"
include "wfn.mm"
include "wa.mm"
include "wb.mm"
include "cpws.mm"
include "cbs.mm"
include "ccrg.mm"
include "cvv.mm"
include "eqid.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "crh.mm"
include "wf.mm"
include "evl1rhm.mm"
include "syl.mm"
include "rhmf.mm"
include "simpld.mm"
include "ffvelrnd.mm"
include "pwselbas.mm"
include "ffnd.mm"
include "fniniseg.mm"
include "mpbir2and.mm"
include "cfn.mm"
include "wss.mm"
include "cen.mm"
include "wbr.mm"
include "c1.mm"
include "cn0.mm"
include "chash.mm"
include "cle.mm"
include "cnvex.mm"
include "imaex.mm"
include "1nn0.mm"
include "cdif.mm"
include "wne.mm"
include "cmgp.mm"
include "cmg.mm"
include "crg.mm"
include "crngring.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulg1.mm"
include "oveq2d.mm"
include "cco1.mm"
include "coe1tmfv1.mm"
include "syl3anc.mm"
include "cxp.mm"
include "coe1z.mm"
include "fveq1d.mm"
include "c0g.mm"
include "fvconst2.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "3netr4d.mm"
include "fveq2.mm"
include "necon3i.mm"
include "eqnetrrd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "mpd.mm"
include "fveq2d.mm"
include "deg1tm.mm"
include "syl121anc.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "hashbnd.mm"
include "ring0cl.mm"
include "cid.mm"
include "cres.mm"
include "cof.mm"
include "cascl.mm"
include "cmulr.mm"
include "ply1sclf.mm"
include "rhmmul.mm"
include "casa.mm"
include "csca.mm"
include "ply1assa.mm"
include "ply1sca.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "asclmul1.mm"
include "pwsmulrval.mm"
include "evl1sca.mm"
include "syl2anc.mm"
include "evl1var.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"
include "fnconstg.mm"
include "fnresi.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "fvconst2g.mm"
include "fvresi.mm"
include "ringrz.mm"
include "snssd.mm"
include "hashsng.mm"
include "cdom.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "snfi.mm"
include "hashdom.mm"
include "mp2an.mm"
include "sylibr.mm"
include "eqbrtrrd.mm"
include "cr.mm"
include "hashcl.mm"
include "nn0red.mm"
include "1re.mm"
include "letri3.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "hashen.mm"
include "sylancr.mm"
include "mpbid.mm"
include "fisseneq.mm"
include "eleqtrrd.mm"
include "elsni.mm"

theorem fta1blem
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume fta1b.p: |- P = ( Poly1 ` R )
  assume fta1b.b: |- B = ( Base ` P )
  assume fta1b.d: |- D = ( deg1 ` R )
  assume fta1b.o: |- O = ( eval1 ` R )
  assume fta1b.w: |- W = ( 0g ` R )
  assume fta1b.z: |- .0. = ( 0g ` P )
  assume fta1blem.k: |- K = ( Base ` R )
  assume fta1blem.t: |- .X. = ( .r ` R )
  assume fta1blem.x: |- X = ( var1 ` R )
  assume fta1blem.s: |- .x. = ( .s ` P )
  assume fta1blem.1: |- ( ph -> R e. CRing )
  assume fta1blem.2: |- ( ph -> M e. K )
  assume fta1blem.3: |- ( ph -> N e. K )
  assume fta1blem.4: |- ( ph -> ( M .X. N ) = W )
  assume fta1blem.5: |- ( ph -> M =/= W )
  assume fta1blem.6: |- ( ph -> ( ( M .x. X ) e. ( B \ { .0. } ) -> ( # ` ( `' ( O ` ( M .x. X ) ) " { W } ) ) <_ ( D ` ( M .x. X ) ) ) )


  assert |- ( ph -> N = W )

  proof
    wph
    cN
    cW
    csn
    #
    wcel
    cN
    cW
    wceq
    wph
    cN
    cM
    cX
    c.x
    co
    #
    cO
    cfv
    #
    ccnv
    #
    @0
    cima
    #
    @0
    wph
    cN
    @4
    wcel
    #
    cN
    cK
    wcel
    #
    cN
    @2
    cfv
    #
    cW
    wceq
    #
    fta1blem.3
    wph
    @7
    cM
    cN
    c.xp
    co
    #
    cW
    wph
    @1
    cB
    wcel
    #
    @7
    @9
    wceq
    #
    wph
    cK
    cP
    cR
    c.x
    c.xp
    cB
    cX
    cM
    cO
    cN
    cN
    fta1b.o
    fta1b.p
    fta1blem.k
    fta1b.b
    fta1blem.1
    fta1blem.3
    wph
    cK
    cP
    cR
    cB
    cO
    cX
    cN
    fta1b.o
    fta1blem.x
    fta1blem.k
    fta1b.p
    fta1b.b
    fta1blem.1
    fta1blem.3
    evl1vard
    fta1blem.2
    fta1blem.s
    fta1blem.t
    evl1vsd
    #
    simprd
    fta1blem.4
    eqtrd
    wph
    @2
    cK
    wfn
    #
    @5
    @6
    @8
    wa
    wb
    wph
    cK
    cK
    @2
    wph
    cK
    cR
    cK
    cR
    cK
    cpws
    co
    #
    cbs
    cfv
    #
    ccrg
    @2
    @14
    cvv
    @14
    eqid
    #
    fta1blem.k
    @15
    eqid
    #
    fta1blem.1
    cK
    cvv
    wcel
    #
    wph
    cK
    cR
    cbs
    cfv
    #
    cvv
    fta1blem.k
    cR
    cbs
    fvex
    eqeltri
    a1i
    #
    wph
    cB
    @15
    @1
    cO
    wph
    cO
    cP
    @14
    crh
    co
    wcel
    #
    cB
    @15
    cO
    wf
    wph
    cR
    ccrg
    wcel
    #
    @21
    fta1blem.1
    cK
    cP
    cR
    @14
    cO
    fta1b.o
    fta1b.p
    @16
    fta1blem.k
    evl1rhm
    syl
    #
    cB
    @15
    cP
    @14
    cO
    fta1b.b
    @17
    rhmf
    syl
    #
    wph
    @10
    @11
    @12
    simpld
    #
    ffvelrnd
    pwselbas
    ffnd
    #
    cK
    cW
    cN
    @2
    fniniseg
    syl
    mpbir2and
    wph
    @4
    cfn
    wcel
    #
    @0
    @4
    wss
    #
    @0
    @4
    cen
    wbr
    #
    @0
    @4
    wceq
    wph
    @4
    cvv
    wcel
    #
    c1
    cn0
    wcel
    #
    @4
    chash
    cfv
    #
    c1
    cle
    wbr
    #
    @27
    @30
    wph
    @3
    @0
    @2
    @1
    cO
    fvex
    cnvex
    imaex
    #
    a1i
    @31
    wph
    1nn0
    a1i
    #
    wph
    @32
    @1
    cD
    cfv
    #
    c1
    cle
    wph
    @1
    cB
    c.0
    csn
    cdif
    wcel
    #
    @32
    @36
    cle
    wbr
    wph
    @10
    @1
    c.0
    wne
    @37
    @25
    wph
    cM
    c1
    cX
    cP
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    c.x
    co
    #
    @1
    c.0
    wph
    @40
    cX
    cM
    c.x
    wph
    cX
    cB
    wcel
    #
    @40
    cX
    wceq
    wph
    cR
    crg
    wcel
    #
    @42
    wph
    @22
    @43
    fta1blem.1
    cR
    crngring
    syl
    #
    cB
    cP
    cR
    cX
    fta1blem.x
    fta1b.p
    fta1b.b
    vr1cl
    syl
    #
    cB
    @39
    @38
    cX
    cB
    cP
    @38
    @38
    eqid
    #
    fta1b.b
    mgpbas
    @39
    eqid
    #
    mulg1
    syl
    oveq2d
    #
    wph
    c1
    @41
    cco1
    cfv
    #
    cfv
    #
    c1
    c.0
    cco1
    cfv
    #
    cfv
    #
    wne
    @41
    c.0
    wne
    wph
    cM
    cW
    @50
    @52
    fta1blem.5
    wph
    @43
    cM
    cK
    wcel
    #
    @31
    @50
    cM
    wceq
    @44
    fta1blem.2
    @35
    cM
    c1
    cP
    cR
    c.x
    @39
    cK
    @38
    cX
    cW
    fta1b.w
    fta1blem.k
    fta1b.p
    fta1blem.x
    fta1blem.s
    @46
    @47
    coe1tmfv1
    syl3anc
    wph
    @52
    c1
    cn0
    @0
    cxp
    #
    cfv
    #
    cW
    wph
    c1
    @51
    @54
    wph
    @43
    @51
    @54
    wceq
    @44
    cP
    cR
    cW
    c.0
    fta1b.p
    fta1b.z
    fta1b.w
    coe1z
    syl
    fveq1d
    @31
    @55
    cW
    wceq
    1nn0
    cn0
    cW
    c1
    cW
    cR
    c0g
    cfv
    cvv
    fta1b.w
    cR
    c0g
    fvex
    eqeltri
    fvconst2
    ax-mp
    syl6eq
    3netr4d
    @41
    c.0
    @50
    @52
    @41
    c.0
    wceq
    c1
    @49
    @51
    @41
    c.0
    cco1
    fveq2
    fveq1d
    necon3i
    syl
    eqnetrrd
    @1
    cB
    c.0
    eldifsn
    sylanbrc
    fta1blem.6
    mpd
    wph
    @41
    cD
    cfv
    #
    @36
    c1
    wph
    @41
    @1
    cD
    @48
    fveq2d
    wph
    @43
    @53
    cM
    cW
    wne
    @31
    @56
    c1
    wceq
    @44
    fta1blem.2
    fta1blem.5
    @35
    cM
    cD
    cP
    cR
    c.x
    @39
    c1
    cK
    @38
    cX
    cW
    fta1b.d
    fta1blem.k
    fta1b.p
    fta1blem.x
    fta1blem.s
    @46
    @47
    fta1b.w
    deg1tm
    syl121anc
    eqtr3d
    breqtrd
    #
    @4
    c1
    cvv
    hashbnd
    syl3anc
    #
    wph
    cW
    @4
    wph
    cW
    @4
    wcel
    #
    cW
    cK
    wcel
    #
    cW
    @2
    cfv
    #
    cW
    wceq
    #
    wph
    @43
    @60
    @44
    cK
    cR
    cW
    fta1blem.k
    fta1b.w
    ring0cl
    syl
    #
    wph
    @61
    cW
    cK
    cM
    csn
    cxp
    #
    cid
    cK
    cres
    #
    c.xp
    cof
    #
    co
    #
    cfv
    #
    cW
    wph
    cW
    @2
    @67
    wph
    cM
    cP
    cascl
    cfv
    #
    cfv
    #
    cX
    cP
    cmulr
    cfv
    #
    co
    #
    cO
    cfv
    #
    @70
    cO
    cfv
    #
    cX
    cO
    cfv
    #
    @14
    cmulr
    cfv
    #
    co
    #
    @2
    @67
    wph
    @21
    @70
    cB
    wcel
    @42
    @73
    @77
    wceq
    @23
    wph
    cK
    cB
    cM
    @69
    wph
    @43
    cK
    cB
    @69
    wf
    @44
    @69
    cB
    cP
    cR
    cK
    fta1b.p
    @69
    eqid
    #
    fta1blem.k
    fta1b.b
    ply1sclf
    syl
    fta1blem.2
    ffvelrnd
    #
    @45
    @70
    cX
    cP
    @14
    @71
    @76
    cO
    cB
    fta1b.b
    @71
    eqid
    #
    @76
    eqid
    #
    rhmmul
    syl3anc
    wph
    @72
    @1
    cO
    wph
    cP
    casa
    wcel
    #
    cM
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @42
    @72
    @1
    wceq
    wph
    @22
    @82
    fta1blem.1
    cP
    cR
    fta1b.p
    ply1assa
    syl
    wph
    cM
    cK
    @84
    fta1blem.2
    wph
    cK
    @19
    @84
    fta1blem.k
    wph
    cR
    @83
    cbs
    wph
    @22
    cR
    @83
    wceq
    fta1blem.1
    cP
    cR
    ccrg
    fta1b.p
    ply1sca
    syl
    fveq2d
    syl5eq
    eleqtrd
    @45
    @69
    cM
    c.x
    @71
    @83
    @84
    cB
    cP
    cX
    @78
    @83
    eqid
    @84
    eqid
    fta1b.b
    @80
    fta1blem.s
    asclmul1
    syl3anc
    fveq2d
    wph
    @77
    @74
    @75
    @66
    co
    @67
    wph
    @15
    cR
    @76
    c.xp
    @74
    @75
    cK
    ccrg
    cvv
    @14
    @16
    @17
    fta1blem.1
    @20
    wph
    cB
    @15
    @70
    cO
    @24
    @79
    ffvelrnd
    wph
    cB
    @15
    cX
    cO
    @24
    @45
    ffvelrnd
    fta1blem.t
    @81
    pwsmulrval
    wph
    @74
    @64
    @75
    @65
    @66
    wph
    @22
    @53
    @74
    @64
    wceq
    fta1blem.1
    fta1blem.2
    @69
    cK
    cP
    cR
    cO
    cM
    fta1b.o
    fta1b.p
    fta1blem.k
    @78
    evl1sca
    syl2anc
    wph
    @22
    @75
    @65
    wceq
    fta1blem.1
    cK
    cR
    cO
    cX
    fta1b.o
    fta1blem.x
    fta1blem.k
    evl1var
    syl
    oveq12d
    eqtrd
    3eqtr3d
    fveq1d
    wph
    @68
    cW
    @64
    cfv
    #
    cW
    @65
    cfv
    #
    c.xp
    co
    #
    cW
    wph
    @64
    cK
    wfn
    #
    @65
    cK
    wfn
    #
    @18
    @60
    @68
    @87
    wceq
    wph
    @53
    @88
    fta1blem.2
    cK
    cM
    cK
    fnconstg
    syl
    @89
    wph
    cK
    fnresi
    a1i
    @20
    @63
    cK
    c.xp
    @64
    @65
    cvv
    cW
    fnfvof
    syl22anc
    wph
    @87
    cM
    cW
    c.xp
    co
    #
    cW
    wph
    @85
    cM
    @86
    cW
    c.xp
    wph
    @53
    @60
    @85
    cM
    wceq
    fta1blem.2
    @63
    cK
    cM
    cW
    cK
    fvconst2g
    syl2anc
    wph
    @60
    @86
    cW
    wceq
    @63
    cK
    cW
    fvresi
    syl
    oveq12d
    wph
    @43
    @53
    @90
    cW
    wceq
    @44
    fta1blem.2
    cK
    cR
    c.xp
    cM
    cW
    fta1blem.k
    fta1blem.t
    fta1b.w
    ringrz
    syl2anc
    eqtrd
    eqtrd
    eqtrd
    wph
    @13
    @59
    @60
    @62
    wa
    wb
    @26
    cK
    cW
    cW
    @2
    fniniseg
    syl
    mpbir2and
    snssd
    #
    wph
    @0
    chash
    cfv
    #
    @32
    wceq
    #
    @29
    wph
    @92
    c1
    @32
    wph
    @60
    @92
    c1
    wceq
    @63
    cW
    cK
    hashsng
    syl
    #
    wph
    @32
    c1
    wceq
    #
    @33
    c1
    @32
    cle
    wbr
    #
    @57
    wph
    @92
    c1
    @32
    cle
    @94
    wph
    @0
    @4
    cdom
    wbr
    #
    @92
    @32
    cle
    wbr
    #
    @30
    wph
    @28
    @97
    @34
    @91
    @0
    @4
    cvv
    ssdomg
    mpsyl
    @0
    cfn
    wcel
    #
    @30
    @98
    @97
    wb
    cW
    snfi
    #
    @34
    @0
    @4
    cvv
    hashdom
    mp2an
    sylibr
    eqbrtrrd
    wph
    @32
    cr
    wcel
    c1
    cr
    wcel
    @95
    @33
    @96
    wa
    wb
    wph
    @32
    wph
    @27
    @32
    cn0
    wcel
    @58
    @4
    hashcl
    syl
    nn0red
    1re
    @32
    c1
    letri3
    sylancl
    mpbir2and
    eqtr4d
    wph
    @99
    @27
    @93
    @29
    wb
    @100
    @58
    @0
    @4
    hashen
    sylancr
    mpbid
    @0
    @4
    fisseneq
    syl3anc
    eleqtrrd
    cN
    cW
    elsni
    syl
end
