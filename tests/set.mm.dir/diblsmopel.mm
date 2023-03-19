include "cop.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "wceq.mm"
include "wex.mm"
include "chlt.mm"
include "clss.mm"
include "wb.mm"
include "wbr.mm"
include "eqid.mm"
include "diblss.mm"
include "syl2anc.mm"
include "dvhopellsm.mm"
include "syl3anc.mm"
include "excom.mm"
include "w3a.mm"
include "dibopelval2.mm"
include "anbi12d.mm"
include "an4.mm"
include "ancom.mm"
include "bitri.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "anass.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "2exbidv.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "cvv.mm"
include "cltrn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "opeq2.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "oveq2d.mm"
include "ceqsex2v.mm"
include "ccom.mm"
include "csca.mm"
include "ctendo.mm"
include "adantr.mm"
include "simprl.mm"
include "diael.mm"
include "tendo0cl.mm"
include "syl.mm"
include "simprr.mm"
include "dvhopvadd.mm"
include "syl122anc.mm"
include "vex.mm"
include "coex.mm"
include "ovex.mm"
include "opth2.mm"
include "dvavadd.mm"
include "syl12anc.mm"
include "bicomd.mm"
include "cmpt2.mm"
include "dvhfplusr.mm"
include "oveqd.mm"
include "tendo0pl.mm"
include "eqtrd.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "exbidv.mm"
include "bicomi.mm"
include "2exbii.mm"
include "19.41vv.mm"
include "wrex.mm"
include "csubg.mm"
include "clvec.mm"
include "clmod.mm"
include "wss.mm"
include "dvalvec.mm"
include "lveclmod.mm"
include "lsssssubg.mm"
include "4syl.mm"
include "dialss.mm"
include "sseldd.mm"
include "lsmelval.mm"
include "r2ex.mm"
include "3bitrd.mm"

theorem diblsmopel
  let wph: wff ph
  let cB: class B
  let c.pb: class .+b
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vs: setvar s
  let vt: setvar t
  assume diblsmopel.b: |- B = ( Base ` K )
  assume diblsmopel.l: |- .<_ = ( le ` K )
  assume diblsmopel.h: |- H = ( LHyp ` K )
  assume diblsmopel.t: |- T = ( ( LTrn ` K ) ` W )
  assume diblsmopel.o: |- O = ( f e. T |-> ( _I |` B ) )
  assume diblsmopel.v: |- V = ( ( DVecA ` K ) ` W )
  assume diblsmopel.u: |- U = ( ( DVecH ` K ) ` W )
  assume diblsmopel.q: |- .(+) = ( LSSum ` V )
  assume diblsmopel.p: |- .+b = ( LSSum ` U )
  assume diblsmopel.j: |- J = ( ( DIsoA ` K ) ` W )
  assume diblsmopel.i: |- I = ( ( DIsoB ` K ) ` W )
  assume diblsmopel.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume diblsmopel.x: |- ( ph -> ( X e. B /\ X .<_ W ) )
  assume diblsmopel.y: |- ( ph -> ( Y e. B /\ Y .<_ W ) )

  disjoint B f
  disjoint H f
  disjoint K f
  disjoint T f
  disjoint W f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint f x
  disjoint f y
  disjoint H x
  disjoint H y
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint f s
  disjoint f t
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint K s
  disjoint t x
  disjoint t y
  disjoint K t
  disjoint K x
  disjoint K y
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T s
  disjoint T t
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint V x
  disjoint V z
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( <. F , S >. e. ( ( I ` X ) .+b ( I ` Y ) ) <-> ( F e. ( ( J ` X ) .(+) ( J ` Y ) ) /\ S = O ) ) )

  proof
    wph
    cF
    cS
    cop
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    c.pb
    co
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @1
    wcel
    #
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    @2
    wcel
    #
    wa
    #
    @0
    @6
    @10
    cU
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vw
    wex
    #
    vz
    wex
    vy
    wex
    #
    vx
    wex
    #
    @4
    cX
    cJ
    cfv
    #
    wcel
    #
    @8
    cY
    cJ
    cfv
    #
    wcel
    #
    wa
    #
    cF
    @4
    @8
    cV
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    cS
    cO
    wceq
    #
    wa
    #
    wa
    #
    vz
    wex
    #
    vx
    wex
    #
    cF
    @20
    @22
    c.po
    co
    wcel
    #
    @28
    wa
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    cU
    clss
    cfv
    #
    wcel
    #
    @2
    @36
    wcel
    #
    @3
    @19
    wb
    diblsmopel.k
    wph
    @35
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    #
    @37
    diblsmopel.k
    diblsmopel.x
    cB
    @36
    cU
    cH
    cI
    cK
    c.le
    cW
    cX
    diblsmopel.b
    diblsmopel.l
    diblsmopel.h
    diblsmopel.u
    diblsmopel.i
    @36
    eqid
    #
    diblss
    syl2anc
    wph
    @35
    cY
    cB
    wcel
    cY
    cW
    c.le
    wbr
    wa
    #
    @38
    diblsmopel.k
    diblsmopel.y
    cB
    @36
    cU
    cH
    cI
    cK
    c.le
    cW
    cY
    diblsmopel.b
    diblsmopel.l
    diblsmopel.h
    diblsmopel.u
    diblsmopel.i
    @40
    diblss
    syl2anc
    vx
    vy
    vz
    vw
    @13
    c.pb
    @36
    cS
    cU
    cF
    cH
    cK
    cW
    @1
    @2
    diblsmopel.h
    diblsmopel.u
    @13
    eqid
    #
    @40
    diblsmopel.p
    dvhopellsm
    syl3anc
    wph
    @18
    @31
    vx
    @18
    @17
    vy
    wex
    #
    vz
    wex
    wph
    @31
    @17
    vy
    vz
    excom
    wph
    @43
    @30
    vz
    wph
    @43
    @5
    cO
    wceq
    #
    @9
    cO
    wceq
    #
    @24
    @15
    wa
    #
    w3a
    #
    vw
    wex
    vy
    wex
    #
    @30
    wph
    @16
    @47
    vy
    vw
    wph
    @16
    @44
    @45
    wa
    #
    @24
    wa
    #
    @15
    wa
    #
    @47
    wph
    @12
    @50
    @15
    wph
    @12
    @21
    @44
    wa
    #
    @23
    @45
    wa
    #
    wa
    #
    @50
    wph
    @7
    @52
    @11
    @53
    wph
    @35
    @39
    @7
    @52
    wb
    diblsmopel.k
    diblsmopel.x
    cB
    @5
    cT
    vf
    @4
    cH
    cI
    cJ
    cK
    c.le
    chlt
    cW
    cX
    cO
    diblsmopel.b
    diblsmopel.l
    diblsmopel.h
    diblsmopel.t
    diblsmopel.o
    diblsmopel.j
    diblsmopel.i
    dibopelval2
    syl2anc
    wph
    @35
    @41
    @11
    @53
    wb
    diblsmopel.k
    diblsmopel.y
    cB
    @9
    cT
    vf
    @8
    cH
    cI
    cJ
    cK
    c.le
    chlt
    cW
    cY
    cO
    diblsmopel.b
    diblsmopel.l
    diblsmopel.h
    diblsmopel.t
    diblsmopel.o
    diblsmopel.j
    diblsmopel.i
    dibopelval2
    syl2anc
    anbi12d
    @54
    @24
    @49
    wa
    @50
    @21
    @44
    @23
    @45
    an4
    @24
    @49
    ancom
    bitri
    syl6bb
    anbi1d
    @51
    @49
    @46
    wa
    @47
    @49
    @24
    @15
    anass
    @44
    @45
    @46
    df-3an
    bitr4i
    syl6bb
    2exbidv
    @48
    @24
    @0
    @4
    cO
    cop
    #
    @8
    cO
    cop
    #
    @13
    co
    #
    wceq
    #
    wa
    #
    wph
    @30
    @46
    @24
    @0
    @55
    @10
    @13
    co
    #
    wceq
    #
    wa
    @59
    vy
    vw
    cO
    cO
    cO
    vf
    cT
    cid
    cB
    cres
    #
    cmpt
    cvv
    diblsmopel.o
    vf
    cT
    @62
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    diblsmopel.t
    cW
    @63
    fvex
    eqeltri
    mptex
    eqeltri
    #
    @64
    @44
    @15
    @61
    @24
    @44
    @14
    @60
    @0
    @44
    @6
    @55
    @10
    @13
    @5
    cO
    @4
    opeq2
    oveq1d
    eqeq2d
    anbi2d
    @45
    @61
    @58
    @24
    @45
    @60
    @57
    @0
    @45
    @10
    @56
    @55
    @13
    @9
    cO
    @8
    opeq2
    oveq2d
    eqeq2d
    anbi2d
    ceqsex2v
    wph
    @24
    @58
    @29
    wph
    @24
    wa
    #
    @58
    @0
    @4
    @8
    ccom
    #
    cO
    cO
    cU
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cop
    #
    wceq
    #
    @29
    @65
    @57
    @70
    @0
    @65
    @35
    @4
    cT
    wcel
    #
    cO
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    #
    @8
    cT
    wcel
    #
    @74
    @57
    @70
    wceq
    wph
    @35
    @24
    diblsmopel.k
    adantr
    #
    @65
    @35
    @39
    @21
    @72
    @76
    wph
    @39
    @24
    diblsmopel.x
    adantr
    wph
    @21
    @23
    simprl
    cB
    cT
    @4
    cH
    cJ
    cK
    c.le
    chlt
    cW
    cX
    diblsmopel.b
    diblsmopel.l
    diblsmopel.h
    diblsmopel.t
    diblsmopel.j
    diael
    syl3anc
    #
    @65
    @35
    @74
    @76
    cB
    cT
    vf
    @73
    cH
    cK
    cO
    cW
    diblsmopel.b
    diblsmopel.h
    diblsmopel.t
    @73
    eqid
    #
    diblsmopel.o
    tendo0cl
    syl
    #
    @65
    @35
    @41
    @23
    @75
    @76
    wph
    @41
    @24
    diblsmopel.y
    adantr
    wph
    @21
    @23
    simprr
    cB
    cT
    @8
    cH
    cJ
    cK
    c.le
    chlt
    cW
    cY
    diblsmopel.b
    diblsmopel.l
    diblsmopel.h
    diblsmopel.t
    diblsmopel.j
    diael
    syl3anc
    #
    @79
    @67
    @13
    @68
    cO
    cO
    cT
    cU
    @73
    @4
    @8
    cH
    cK
    cW
    diblsmopel.h
    diblsmopel.t
    @78
    diblsmopel.u
    @67
    eqid
    #
    @42
    @68
    eqid
    #
    dvhopvadd
    syl122anc
    eqeq2d
    @71
    cF
    @66
    wceq
    #
    cS
    @69
    wceq
    #
    wa
    @65
    @29
    cF
    cS
    @66
    @69
    @4
    @8
    vx
    vex
    vz
    vex
    coex
    cO
    cO
    @68
    ovex
    opth2
    @65
    @83
    @27
    @84
    @28
    @65
    @27
    @83
    @65
    @26
    @66
    cF
    @65
    @35
    @72
    @75
    @26
    @66
    wceq
    @76
    @77
    @80
    @25
    cT
    cV
    @4
    @8
    cH
    cK
    chlt
    cW
    diblsmopel.h
    diblsmopel.t
    diblsmopel.v
    @25
    eqid
    #
    dvavadd
    syl12anc
    eqeq2d
    bicomd
    @65
    @69
    cO
    cS
    @65
    @69
    cO
    cO
    vs
    vt
    @73
    @73
    vf
    cT
    vf
    cv
    #
    vs
    cv
    cfv
    @86
    vt
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    co
    #
    cO
    @65
    @68
    @87
    cO
    cO
    @65
    @35
    @68
    @87
    wceq
    @76
    vt
    @87
    @68
    cT
    cU
    vf
    @73
    @67
    cH
    cK
    chlt
    cW
    vs
    diblsmopel.h
    diblsmopel.t
    @78
    diblsmopel.u
    @81
    @87
    eqid
    #
    @82
    dvhfplusr
    syl
    oveqd
    @65
    @35
    @74
    @88
    cO
    wceq
    @76
    @79
    vt
    cB
    @87
    cO
    cT
    vf
    @73
    cH
    cK
    cO
    cW
    vs
    diblsmopel.b
    diblsmopel.h
    diblsmopel.t
    @78
    diblsmopel.o
    @89
    tendo0pl
    syl2anc
    eqtrd
    eqeq2d
    anbi12d
    syl5bb
    bitrd
    pm5.32da
    syl5bb
    bitrd
    exbidv
    syl5bb
    exbidv
    @32
    @24
    @27
    wa
    #
    vz
    wex
    vx
    wex
    #
    @28
    wa
    #
    wph
    @34
    @32
    @90
    @28
    wa
    #
    vz
    wex
    vx
    wex
    @92
    @30
    @93
    vx
    vz
    @93
    @30
    @24
    @27
    @28
    anass
    bicomi
    2exbii
    @90
    @28
    vx
    vz
    19.41vv
    bitri
    wph
    @34
    @92
    wph
    @33
    @91
    @28
    wph
    @33
    @27
    vz
    @22
    wrex
    vx
    @20
    wrex
    #
    @91
    wph
    @20
    cV
    csubg
    cfv
    #
    wcel
    @22
    @95
    wcel
    @33
    @94
    wb
    wph
    cV
    clss
    cfv
    #
    @95
    @20
    wph
    @35
    cV
    clvec
    wcel
    cV
    clmod
    wcel
    @96
    @95
    wss
    diblsmopel.k
    cV
    cH
    cK
    cW
    diblsmopel.h
    diblsmopel.v
    dvalvec
    cV
    lveclmod
    @96
    cV
    @96
    eqid
    #
    lsssssubg
    4syl
    #
    wph
    @35
    @39
    @20
    @96
    wcel
    diblsmopel.k
    diblsmopel.x
    cB
    @96
    cV
    cH
    cJ
    cK
    c.le
    cW
    cX
    diblsmopel.b
    diblsmopel.l
    diblsmopel.h
    diblsmopel.v
    diblsmopel.j
    @97
    dialss
    syl2anc
    sseldd
    wph
    @96
    @95
    @22
    @98
    wph
    @35
    @41
    @22
    @96
    wcel
    diblsmopel.k
    diblsmopel.y
    cB
    @96
    cV
    cH
    cJ
    cK
    c.le
    cW
    cY
    diblsmopel.b
    diblsmopel.l
    diblsmopel.h
    diblsmopel.v
    diblsmopel.j
    @97
    dialss
    syl2anc
    sseldd
    vx
    vz
    @25
    c.po
    @20
    @22
    cV
    cF
    @85
    diblsmopel.q
    lsmelval
    syl2anc
    @27
    vx
    vz
    @20
    @22
    r2ex
    syl6bb
    anbi1d
    bicomd
    syl5bb
    3bitrd
end
