include "cfv.mm"
include "co.mm"
include "c0.mm"
include "cop.mm"
include "cs2.mm"
include "cv.mm"
include "crn.mm"
include "ciun.mm"
include "cdif.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "wcel.mm"
include "c1o.mm"
include "cpr.mm"
include "0ex.mm"
include "prid1.mm"
include "df2o3.mm"
include "eleqtrri.mm"
include "opelxpi.mm"
include "sylancl.mm"
include "s2cld.mm"
include "cid.mm"
include "cvv.mm"
include "wceq.mm"
include "con0.mm"
include "2on.mm"
include "xpexg.mm"
include "wrdexg.mm"
include "fvi.mm"
include "3syl.mm"
include "syl5eq.mm"
include "eleqtrrd.mm"
include "wrex.mm"
include "wa.mm"
include "wne.mm"
include "wn.mm"
include "1n0.mm"
include "cc0.mm"
include "chash.mm"
include "c2.mm"
include "caddc.mm"
include "2cn.mm"
include "addid2i.mm"
include "s2len.mm"
include "eqtr4i.mm"
include "efgtlen.mm"
include "adantll.mm"
include "ex.mm"
include "0cnd.mm"
include "cn0.mm"
include "simpr.mm"
include "efgrcl.mm"
include "simprd.mm"
include "adantl.mm"
include "eleqtrd.mm"
include "lencl.mm"
include "syl.mm"
include "nn0cnd.mm"
include "2cnd.mm"
include "addcan2d.mm"
include "sylibd.mm"
include "wi.mm"
include "cfz.mm"
include "cotp.mm"
include "csplice.mm"
include "cmpt2.mm"
include "wf.mm"
include "efgtf.mm"
include "simpld.mm"
include "rneqd.mm"
include "eleq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "elrnmpt2.mm"
include "cconcat.mm"
include "wrd0.mm"
include "a1i.mm"
include "simprr.mm"
include "efgmf.mm"
include "ffvelrni.mm"
include "ccatlid.mm"
include "ax-mp.mm"
include "oveq1i.mm"
include "eqtr2i.mm"
include "simprl.mm"
include "hash0.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "elfz1eq.mm"
include "syl6eqr.mm"
include "cc.mm"
include "0cn.mm"
include "syl6eqel.mm"
include "addid1d.mm"
include "syl5req.mm"
include "splval2.mm"
include "oveq1d.mm"
include "ccatrid.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "ad3antrrr.mm"
include "1on.mm"
include "c1.mm"
include "fveq1d.mm"
include "opex.mm"
include "s2fv1.mm"
include "fvex.mm"
include "3eqtr3g.mm"
include "s2fv0.mm"
include "vex.mm"
include "fveq2d.mm"
include "efgmval.mm"
include "df-ov.mm"
include "dif0.mm"
include "opeq2i.mm"
include "3eqtr2rd.mm"
include "opthg.mm"
include "simplbda.mm"
include "syl21anc.mm"
include "sylbid.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "wb.mm"
include "hasheq0.mm"
include "eleq1.mm"
include "fveq2.mm"
include "anbi12d.mm"
include "sylbi.mm"
include "eqcoms.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "com23.mm"
include "expdimp.mm"
include "mpdd.mm"
include "necon3ad.mm"
include "mpi.mm"
include "nrexdv.mm"
include "eliun.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "syl6eleqr.mm"
include "cs1.mm"
include "cec.mm"
include "wbr.mm"
include "df-s2.mm"
include "wer.mm"
include "efger.mm"
include "erref.mm"
include "syl5eqbrr.mm"
include "eqeltri.mm"
include "elec.mm"
include "sylibr.mm"
include "vrgpval.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "s1cld.mm"
include "frgpadd.mm"
include "elind.mm"

theorem frgpnabllem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.sm: class .~
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cG: class G
  let cI: class I
  let cM: class M
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vm: setvar m
  let vt: setvar t
  let vk: setvar k
  assume frgpnabl.g: |- G = ( freeGrp ` I )
  assume frgpnabl.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume frgpnabl.r: |- .~ = ( ~FG ` I )
  assume frgpnabl.p: |- .+ = ( +g ` G )
  assume frgpnabl.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )
  assume frgpnabl.t: |- T = ( v e. W |-> ( n e. ( 0 ... ( # ` v ) ) , w e. ( I X. 2o ) |-> ( v splice <. n , n , <" w ( M ` w ) "> >. ) ) )
  assume frgpnabl.d: |- D = ( W \ U_ x e. W ran ( T ` x ) )
  assume frgpnabl.u: |- U = ( varFGrp ` I )
  assume frgpnabl.i: |- ( ph -> I e. _V )
  assume frgpnabl.a: |- ( ph -> A e. I )
  assume frgpnabl.b: |- ( ph -> B e. I )

  disjoint A x
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint I n
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint I v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint x y
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint ph x
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint B x
  disjoint W n
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint G x
  disjoint M n
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint T x
  disjoint a b
  disjoint a d
  disjoint a x
  disjoint A a
  disjoint b d
  disjoint b x
  disjoint A b
  disjoint d x
  disjoint A d
  disjoint d m
  disjoint d t
  disjoint D d
  disjoint m t
  disjoint D m
  disjoint D t
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a v
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint I a
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b v
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint I b
  disjoint m n
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint I m
  disjoint n t
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint I t
  disjoint a ph
  disjoint b ph
  disjoint .~ a
  disjoint .~ b
  disjoint d y
  disjoint d z
  disjoint .~ d
  disjoint .~ m
  disjoint .~ t
  disjoint B a
  disjoint B b
  disjoint B d
  disjoint a k
  disjoint W a
  disjoint b k
  disjoint W b
  disjoint d k
  disjoint d n
  disjoint d v
  disjoint d w
  disjoint W d
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint W k
  disjoint W m
  disjoint W t
  disjoint G a
  disjoint G b
  disjoint M a
  disjoint M b
  disjoint M m
  disjoint M t
  disjoint T a
  disjoint T b
  disjoint T d
  disjoint T k
  disjoint T m
  disjoint T t
  assert |- ( ph -> <" <. A , (/) >. <. B , (/) >. "> e. ( D i^i ( ( U ` A ) .+ ( U ` B ) ) ) )

  proof
    wph
    cD
    cA
    cU
    cfv
    #
    cB
    cU
    cfv
    #
    c.pl
    co
    #
    cA
    c0
    cop
    #
    cB
    c0
    cop
    #
    cs2
    #
    wph
    @5
    cW
    vx
    cW
    vx
    cv
    #
    cT
    cfv
    #
    crn
    #
    ciun
    #
    cdif
    cD
    wph
    @5
    cW
    @9
    wph
    @5
    cI
    c2o
    cxp
    #
    cword
    #
    cW
    wph
    @3
    @4
    @10
    wph
    cA
    cI
    wcel
    #
    c0
    c2o
    wcel
    #
    @3
    @10
    wcel
    frgpnabl.a
    c0
    c0
    c1o
    cpr
    c2o
    c0
    c1o
    0ex
    prid1
    df2o3
    eleqtrri
    #
    cA
    c0
    cI
    c2o
    opelxpi
    sylancl
    #
    wph
    cB
    cI
    wcel
    #
    @13
    @4
    @10
    wcel
    frgpnabl.b
    @14
    cB
    c0
    cI
    c2o
    opelxpi
    sylancl
    #
    s2cld
    wph
    cW
    @11
    cid
    cfv
    #
    @11
    frgpnabl.w
    wph
    @10
    cvv
    wcel
    #
    @11
    cvv
    wcel
    @18
    @11
    wceq
    wph
    cI
    cvv
    wcel
    #
    c2o
    con0
    wcel
    @19
    frgpnabl.i
    2on
    cI
    c2o
    cvv
    con0
    xpexg
    sylancl
    @10
    cvv
    wrdexg
    @11
    cvv
    fvi
    3syl
    syl5eq
    #
    eleqtrrd
    #
    wph
    @5
    @8
    wcel
    #
    vx
    cW
    wrex
    @5
    @9
    wcel
    wph
    @23
    vx
    cW
    wph
    @6
    cW
    wcel
    #
    wa
    #
    c1o
    c0
    wne
    @23
    wn
    1n0
    @25
    @23
    c1o
    c0
    @25
    @23
    cc0
    @6
    chash
    cfv
    #
    wceq
    #
    c1o
    c0
    wceq
    #
    @25
    @23
    cc0
    c2
    caddc
    co
    #
    @26
    c2
    caddc
    co
    #
    wceq
    #
    @27
    @25
    @23
    @31
    @25
    @23
    wa
    @29
    @5
    chash
    cfv
    #
    @30
    @29
    c2
    @32
    c2
    2cn
    addid2i
    @3
    @4
    s2len
    eqtr4i
    @24
    @23
    @32
    @30
    wceq
    wph
    vy
    vz
    vw
    vv
    @5
    c.sm
    cT
    vn
    cI
    cM
    cW
    @6
    frgpnabl.w
    frgpnabl.r
    frgpnabl.m
    frgpnabl.t
    efgtlen
    adantll
    syl5eq
    ex
    @25
    cc0
    @26
    c2
    @25
    0cnd
    @25
    @26
    @25
    @6
    @11
    wcel
    @26
    cn0
    wcel
    @25
    @6
    cW
    @11
    wph
    @24
    simpr
    @24
    cW
    @11
    wceq
    #
    wph
    @24
    @20
    @33
    @6
    cI
    cW
    frgpnabl.w
    efgrcl
    simprd
    adantl
    eleqtrd
    @10
    @6
    lencl
    syl
    nn0cnd
    @25
    2cnd
    addcan2d
    sylibd
    wph
    @24
    @23
    @27
    @28
    wi
    wph
    @27
    @24
    @23
    wa
    #
    @28
    wph
    @34
    @28
    wi
    @27
    c0
    cW
    wcel
    #
    @5
    c0
    cT
    cfv
    #
    crn
    #
    wcel
    #
    wa
    #
    @28
    wi
    wph
    @35
    @38
    @28
    wph
    @35
    wa
    #
    @38
    @5
    va
    vb
    cc0
    c0
    chash
    cfv
    #
    cfz
    co
    #
    @10
    c0
    va
    cv
    #
    @43
    vb
    cv
    #
    @44
    cM
    cfv
    #
    cs2
    #
    cotp
    #
    csplice
    co
    #
    cmpt2
    #
    crn
    #
    wcel
    #
    @28
    @40
    @37
    @50
    @5
    @40
    @36
    @49
    @40
    @36
    @49
    wceq
    #
    @42
    @10
    cxp
    cW
    @36
    wf
    #
    @35
    @52
    @53
    wa
    wph
    vy
    vz
    vw
    vv
    c.sm
    cT
    vn
    cI
    cM
    cW
    c0
    va
    vb
    frgpnabl.w
    frgpnabl.r
    frgpnabl.m
    frgpnabl.t
    efgtf
    adantl
    simpld
    rneqd
    eleq2d
    @51
    @5
    @48
    wceq
    #
    vb
    @10
    wrex
    va
    @42
    wrex
    @40
    @28
    va
    vb
    @42
    @10
    @48
    @5
    @49
    @49
    eqid
    c0
    @47
    csplice
    ovex
    elrnmpt2
    @40
    @54
    @28
    va
    vb
    @42
    @10
    @40
    @43
    @42
    wcel
    #
    @44
    @10
    wcel
    #
    wa
    #
    wa
    #
    @54
    @5
    @46
    wceq
    #
    @28
    @58
    @48
    @46
    @5
    @58
    @48
    c0
    @46
    cconcat
    co
    #
    c0
    cconcat
    co
    #
    @46
    @58
    c0
    c0
    c0
    @46
    c0
    @43
    @43
    @10
    c0
    @11
    wcel
    #
    @58
    @10
    wrd0
    #
    a1i
    #
    @64
    @64
    @58
    @44
    @45
    @10
    @40
    @55
    @56
    simprr
    #
    @58
    @56
    @45
    @10
    wcel
    @65
    @10
    @10
    @44
    cM
    vy
    vz
    cI
    cM
    frgpnabl.m
    efgmf
    ffvelrni
    syl
    s2cld
    #
    c0
    c0
    c0
    cconcat
    co
    #
    c0
    cconcat
    co
    #
    wceq
    @58
    @68
    @67
    c0
    @67
    c0
    c0
    cconcat
    @62
    @67
    c0
    wceq
    @63
    @10
    c0
    ccatlid
    ax-mp
    #
    oveq1i
    @69
    eqtr2i
    a1i
    @58
    @43
    cc0
    @41
    @58
    @43
    cc0
    cc0
    cfz
    co
    #
    wcel
    @43
    cc0
    wceq
    @58
    @43
    @42
    @70
    @40
    @55
    @56
    simprl
    @41
    cc0
    cc0
    cfz
    hash0
    oveq2i
    syl6eleq
    @43
    cc0
    elfz1eq
    syl
    #
    hash0
    syl6eqr
    @58
    @43
    @41
    caddc
    co
    @43
    cc0
    caddc
    co
    @43
    @41
    cc0
    @43
    caddc
    hash0
    oveq2i
    @58
    @43
    @58
    @43
    cc0
    cc
    @71
    0cn
    syl6eqel
    addid1d
    syl5req
    splval2
    @58
    @46
    @11
    wcel
    #
    @61
    @46
    wceq
    @66
    @72
    @61
    @46
    c0
    cconcat
    co
    @46
    @72
    @60
    @46
    c0
    cconcat
    @10
    @46
    ccatlid
    oveq1d
    @10
    @46
    ccatrid
    eqtrd
    syl
    eqtrd
    eqeq2d
    @58
    @59
    @28
    @58
    @59
    wa
    #
    @12
    c1o
    con0
    wcel
    #
    cA
    c1o
    cop
    #
    @4
    wceq
    #
    @28
    wph
    @12
    @35
    @57
    @59
    frgpnabl.a
    ad3antrrr
    #
    @74
    @73
    1on
    a1i
    @73
    @4
    @45
    @3
    cM
    cfv
    #
    @75
    @73
    c1
    @5
    cfv
    #
    c1
    @46
    cfv
    #
    @4
    @45
    @73
    c1
    @5
    @46
    @58
    @59
    simpr
    #
    fveq1d
    @4
    cvv
    wcel
    @79
    @4
    wceq
    cB
    c0
    opex
    @3
    @4
    cvv
    s2fv1
    ax-mp
    @45
    cvv
    wcel
    @80
    @45
    wceq
    @44
    cM
    fvex
    @44
    @45
    cvv
    s2fv1
    ax-mp
    3eqtr3g
    @73
    @3
    @44
    cM
    @73
    cc0
    @5
    cfv
    #
    cc0
    @46
    cfv
    #
    @3
    @44
    @73
    cc0
    @5
    @46
    @81
    fveq1d
    @3
    cvv
    wcel
    @82
    @3
    wceq
    cA
    c0
    opex
    @3
    @4
    cvv
    s2fv0
    ax-mp
    @44
    cvv
    wcel
    @83
    @44
    wceq
    vb
    vex
    @44
    @45
    cvv
    s2fv0
    ax-mp
    3eqtr3g
    fveq2d
    @73
    cA
    c0
    cM
    co
    #
    cA
    c1o
    c0
    cdif
    #
    cop
    #
    @78
    @75
    @73
    @12
    @13
    @84
    @86
    wceq
    @77
    @14
    vy
    vz
    cA
    c0
    cI
    cM
    frgpnabl.m
    efgmval
    sylancl
    cA
    c0
    cM
    df-ov
    @85
    c1o
    cA
    c1o
    dif0
    opeq2i
    3eqtr3g
    3eqtr2rd
    @12
    @74
    wa
    @76
    cA
    cB
    wceq
    @28
    cA
    c1o
    cB
    c0
    cI
    con0
    opthg
    simplbda
    syl21anc
    ex
    sylbid
    rexlimdvva
    syl5bi
    sylbid
    expimpd
    @27
    @34
    @39
    @28
    @34
    @39
    wb
    #
    @26
    cc0
    @26
    cc0
    wceq
    #
    @6
    c0
    wceq
    #
    @87
    @6
    cvv
    wcel
    @88
    @89
    wb
    vx
    vex
    @6
    cvv
    hasheq0
    ax-mp
    @89
    @24
    @35
    @23
    @38
    @6
    c0
    cW
    eleq1
    @89
    @8
    @37
    @5
    @89
    @7
    @36
    @6
    c0
    cT
    fveq2
    rneqd
    eleq2d
    anbi12d
    sylbi
    eqcoms
    imbi1d
    syl5ibrcom
    com23
    expdimp
    mpdd
    necon3ad
    mpi
    nrexdv
    vx
    @5
    cW
    @8
    eliun
    sylnibr
    eldifd
    frgpnabl.d
    syl6eleqr
    wph
    @5
    @3
    cs1
    #
    @4
    cs1
    #
    cconcat
    co
    #
    c.sm
    cec
    #
    @2
    wph
    @92
    @5
    c.sm
    wbr
    @5
    @93
    wcel
    wph
    @92
    @5
    @5
    c.sm
    @3
    @4
    df-s2
    #
    wph
    @5
    c.sm
    cW
    cW
    c.sm
    wer
    wph
    c.sm
    cI
    cW
    frgpnabl.w
    frgpnabl.r
    efger
    a1i
    @22
    erref
    syl5eqbrr
    @5
    @92
    c.sm
    @5
    @92
    cvv
    @94
    @90
    @91
    cconcat
    ovex
    #
    eqeltri
    @95
    elec
    sylibr
    wph
    @2
    @90
    c.sm
    cec
    #
    @91
    c.sm
    cec
    #
    c.pl
    co
    #
    @93
    wph
    @0
    @96
    @1
    @97
    c.pl
    wph
    @20
    @12
    @0
    @96
    wceq
    frgpnabl.i
    frgpnabl.a
    cA
    c.sm
    cU
    cI
    cvv
    frgpnabl.r
    frgpnabl.u
    vrgpval
    syl2anc
    wph
    @20
    @16
    @1
    @97
    wceq
    frgpnabl.i
    frgpnabl.b
    cB
    c.sm
    cU
    cI
    cvv
    frgpnabl.r
    frgpnabl.u
    vrgpval
    syl2anc
    oveq12d
    wph
    @90
    cW
    wcel
    @91
    cW
    wcel
    @98
    @93
    wceq
    wph
    @90
    @11
    cW
    wph
    @3
    @10
    @15
    s1cld
    @21
    eleqtrrd
    wph
    @91
    @11
    cW
    wph
    @4
    @10
    @17
    s1cld
    @21
    eleqtrrd
    @90
    @91
    c.pl
    c.sm
    cG
    cI
    cW
    frgpnabl.w
    frgpnabl.g
    frgpnabl.r
    frgpnabl.p
    frgpadd
    syl2anc
    eqtrd
    eleqtrrd
    elind
end
