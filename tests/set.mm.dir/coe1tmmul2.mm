include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "cfz.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "ply1tmcl.mm"
include "syl3anc.mm"
include "coe1mul.mm"
include "wa.mm"
include "eqeq2.mm"
include "cvv.mm"
include "cmnd.mm"
include "adantr.mm"
include "ringmnd.mm"
include "syl.mm"
include "ovex.mm"
include "a1i.mm"
include "simprr.mm"
include "wb.mm"
include "simprl.mm"
include "nn0sub.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "nn0ge0d.mm"
include "cr.mm"
include "nn0re.mm"
include "ad2antrl.mm"
include "nn0red.mm"
include "subge02d.mm"
include "fznn0.mm"
include "mpbir2and.mm"
include "ad2antrr.mm"
include "wf.mm"
include "eqid.mm"
include "coe1f.mm"
include "elfznn0.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "fznn0sub.mm"
include "ringcl.mm"
include "fmptd.mm"
include "csn.mm"
include "cdif.mm"
include "eldifi.mm"
include "wne.mm"
include "eldifsn.mm"
include "simplrl.mm"
include "nn0cnd.mm"
include "cc.mm"
include "nncand.mm"
include "eqcomd.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "impr.mm"
include "sylan2b.mm"
include "coe1tmfv2.mm"
include "oveq2d.mm"
include "ringrz.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "suppss2.mm"
include "gsumpt.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "fvmpt.mm"
include "coe1tmfv1.mm"
include "3eqtrd.mm"
include "anassrs.mm"
include "wn.mm"
include "ad2antll.mm"
include "ad2antlr.mm"
include "clt.mm"
include "ltnled.mm"
include "mpbird.mm"
include "lelttrd.mm"
include "gtned.mm"
include "mpteq2dva.mm"
include "gsumz.mm"
include "sylancl.mm"
include "ifbothda.mm"

theorem coe1tmmul2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let c.xp: class .X.
  let c.ex: class .^
  let cK: class K
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let cF: class F
  let cY: class Y
  assume coe1tm.z: |- .0. = ( 0g ` R )
  assume coe1tm.k: |- K = ( Base ` R )
  assume coe1tm.p: |- P = ( Poly1 ` R )
  assume coe1tm.x: |- X = ( var1 ` R )
  assume coe1tm.m: |- .x. = ( .s ` P )
  assume coe1tm.n: |- N = ( mulGrp ` P )
  assume coe1tm.e: |- .^ = ( .g ` N )
  assume coe1tmmul.b: |- B = ( Base ` P )
  assume coe1tmmul.t: |- .xb = ( .r ` P )
  assume coe1tmmul.u: |- .X. = ( .r ` R )
  assume coe1tmmul.a: |- ( ph -> A e. B )
  assume coe1tmmul.r: |- ( ph -> R e. Ring )
  assume coe1tmmul.c: |- ( ph -> C e. K )
  assume coe1tmmul.d: |- ( ph -> D e. NN0 )

  disjoint .0. x
  disjoint C x
  disjoint D x
  disjoint K x
  disjoint .^ x
  disjoint A x
  disjoint N x
  disjoint P x
  disjoint X x
  disjoint ph x
  disjoint R x
  disjoint .x. x
  disjoint .X. x
  disjoint .xb x
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint .0. a
  disjoint b x
  disjoint b y
  disjoint .0. b
  disjoint x y
  disjoint .0. y
  disjoint C b
  disjoint C y
  disjoint D a
  disjoint D b
  disjoint D y
  disjoint F x
  disjoint K b
  disjoint K y
  disjoint .^ y
  disjoint A y
  disjoint N y
  disjoint P y
  disjoint X y
  disjoint Y x
  disjoint ph y
  disjoint R a
  disjoint R b
  disjoint R y
  disjoint .x. y
  disjoint .X. y
  assert |- ( ph -> ( coe1 ` ( A .xb ( C .x. ( D .^ X ) ) ) ) = ( x e. NN0 |-> if ( D <_ x , ( ( ( coe1 ` A ) ` ( x - D ) ) .X. C ) , .0. ) ) )

  proof
    wph
    cA
    cC
    cD
    cX
    c.ex
    co
    c.x
    co
    #
    c.xb
    co
    cco1
    cfv
    #
    vx
    cn0
    cR
    vy
    cc0
    vx
    cv
    #
    cfz
    co
    #
    vy
    cv
    #
    cA
    cco1
    cfv
    #
    cfv
    #
    @2
    @4
    cmin
    co
    #
    @0
    cco1
    cfv
    #
    cfv
    #
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    vx
    cn0
    cD
    @2
    cle
    wbr
    #
    @2
    cD
    cmin
    co
    #
    @5
    cfv
    #
    cC
    c.xp
    co
    #
    c.0
    cif
    #
    cmpt
    wph
    cR
    crg
    wcel
    #
    cA
    cB
    wcel
    #
    @0
    cB
    wcel
    #
    @1
    @13
    wceq
    coe1tmmul.r
    coe1tmmul.a
    wph
    @19
    cC
    cK
    wcel
    #
    cD
    cn0
    wcel
    #
    @21
    coe1tmmul.r
    coe1tmmul.c
    coe1tmmul.d
    cB
    cC
    cD
    cP
    cR
    c.x
    c.ex
    cK
    cN
    cX
    coe1tm.k
    coe1tm.p
    coe1tm.x
    coe1tm.m
    coe1tm.n
    coe1tm.e
    coe1tmmul.b
    ply1tmcl
    syl3anc
    #
    vy
    cB
    cR
    c.xb
    c.xp
    vx
    cA
    @0
    cP
    coe1tm.p
    coe1tmmul.t
    coe1tmmul.u
    coe1tmmul.b
    coe1mul
    syl3anc
    wph
    vx
    cn0
    @12
    @18
    @14
    @12
    @17
    wceq
    #
    @12
    c.0
    wceq
    @12
    @18
    wceq
    wph
    @2
    cn0
    wcel
    #
    wa
    #
    @17
    c.0
    @17
    @18
    @12
    eqeq2
    c.0
    @18
    @12
    eqeq2
    wph
    @26
    @14
    @25
    wph
    @26
    @14
    wa
    #
    wa
    #
    @12
    @15
    @11
    cfv
    #
    @16
    @2
    @15
    cmin
    co
    #
    @8
    cfv
    #
    c.xp
    co
    #
    @17
    @29
    @3
    cK
    @11
    cR
    cvv
    @15
    c.0
    coe1tm.k
    coe1tm.z
    @29
    @19
    cR
    cmnd
    wcel
    #
    wph
    @19
    @28
    coe1tmmul.r
    adantr
    #
    cR
    ringmnd
    #
    syl
    @3
    cvv
    wcel
    #
    @29
    cc0
    @2
    cfz
    ovex
    #
    a1i
    #
    @29
    @15
    @3
    wcel
    #
    @15
    cn0
    wcel
    #
    @15
    @2
    cle
    wbr
    #
    @29
    @14
    @41
    wph
    @26
    @14
    simprr
    @29
    @23
    @26
    @14
    @41
    wb
    wph
    @23
    @28
    coe1tmmul.d
    adantr
    #
    wph
    @26
    @14
    simprl
    #
    cD
    @2
    nn0sub
    syl2anc
    mpbid
    @29
    cc0
    cD
    cle
    wbr
    @42
    @29
    cD
    @43
    nn0ge0d
    @29
    @2
    cD
    @26
    @2
    cr
    wcel
    #
    wph
    @14
    @2
    nn0re
    #
    ad2antrl
    wph
    cD
    cr
    wcel
    #
    @28
    wph
    cD
    coe1tmmul.d
    nn0red
    #
    adantr
    subge02d
    mpbid
    @26
    @40
    @41
    @42
    wa
    wb
    wph
    @14
    @15
    @2
    fznn0
    ad2antrl
    mpbir2and
    #
    @29
    vy
    @3
    @10
    cK
    @11
    @29
    @4
    @3
    wcel
    #
    wa
    #
    @19
    @6
    cK
    wcel
    #
    @9
    cK
    wcel
    @10
    cK
    wcel
    wph
    @19
    @28
    @50
    coe1tmmul.r
    ad2antrr
    #
    @51
    cn0
    cK
    @4
    @5
    wph
    cn0
    cK
    @5
    wf
    #
    @28
    @50
    wph
    @20
    @54
    coe1tmmul.a
    @5
    cB
    cP
    cR
    cA
    cK
    @5
    eqid
    coe1tmmul.b
    coe1tm.p
    coe1tm.k
    coe1f
    syl
    #
    ad2antrr
    @50
    @4
    cn0
    wcel
    #
    @29
    @4
    @2
    elfznn0
    #
    adantl
    ffvelrnd
    #
    @51
    cn0
    cK
    @7
    @8
    wph
    cn0
    cK
    @8
    wf
    #
    @28
    @50
    wph
    @21
    @59
    @24
    @8
    cB
    cP
    cR
    @0
    cK
    @8
    eqid
    coe1tmmul.b
    coe1tm.p
    coe1tm.k
    coe1f
    syl
    ad2antrr
    @50
    @7
    cn0
    wcel
    #
    @29
    @4
    cc0
    @2
    fznn0sub
    #
    adantl
    ffvelrnd
    cK
    cR
    c.xp
    @6
    @9
    coe1tm.k
    coe1tmmul.u
    ringcl
    syl3anc
    @11
    eqid
    #
    fmptd
    @29
    @3
    @10
    vy
    cvv
    @15
    csn
    #
    c.0
    @29
    @4
    @3
    @63
    cdif
    wcel
    #
    wa
    #
    @10
    @6
    c.0
    c.xp
    co
    #
    c.0
    @65
    @9
    c.0
    @6
    c.xp
    @65
    cC
    cD
    cP
    cR
    c.x
    c.ex
    @7
    cK
    cN
    cX
    c.0
    coe1tm.z
    coe1tm.k
    coe1tm.p
    coe1tm.x
    coe1tm.m
    coe1tm.n
    coe1tm.e
    wph
    @19
    @28
    @64
    coe1tmmul.r
    ad2antrr
    wph
    @22
    @28
    @64
    coe1tmmul.c
    ad2antrr
    wph
    @23
    @28
    @64
    coe1tmmul.d
    ad2antrr
    @64
    @60
    @29
    @64
    @50
    @60
    @4
    @3
    @63
    eldifi
    #
    @61
    syl
    adantl
    @64
    @29
    @50
    @4
    @15
    wne
    #
    wa
    cD
    @7
    wne
    #
    @4
    @3
    @15
    eldifsn
    @29
    @50
    @68
    @69
    @51
    cD
    @7
    @4
    @15
    @51
    @4
    @15
    wceq
    #
    cD
    @7
    wceq
    #
    @4
    @2
    @7
    cmin
    co
    #
    wceq
    @51
    @72
    @4
    @51
    @2
    @4
    @51
    @2
    wph
    @26
    @14
    @50
    simplrl
    nn0cnd
    @50
    @4
    cc
    wcel
    @29
    @50
    @4
    @57
    nn0cnd
    adantl
    nncand
    eqcomd
    @71
    @15
    @72
    @4
    cD
    @7
    @2
    cmin
    oveq2
    eqeq2d
    syl5ibrcom
    necon3d
    impr
    sylan2b
    coe1tmfv2
    oveq2d
    @64
    @29
    @50
    @66
    c.0
    wceq
    #
    @67
    @51
    @19
    @52
    @73
    @53
    @58
    cK
    cR
    c.xp
    @6
    c.0
    coe1tm.k
    coe1tmmul.u
    coe1tm.z
    ringrz
    #
    syl2anc
    sylan2
    eqtrd
    @39
    suppss2
    gsumpt
    @29
    @40
    @30
    @33
    wceq
    @49
    vy
    @15
    @10
    @33
    @3
    @11
    @70
    @6
    @16
    @9
    @32
    c.xp
    @4
    @15
    @5
    fveq2
    @70
    @7
    @31
    @8
    @4
    @15
    @2
    cmin
    oveq2
    fveq2d
    oveq12d
    @62
    @16
    @32
    c.xp
    ovex
    fvmpt
    syl
    @29
    @32
    cC
    @16
    c.xp
    @29
    @32
    cD
    @8
    cfv
    #
    cC
    @29
    @31
    cD
    @8
    @29
    @2
    cD
    @29
    @2
    @44
    nn0cnd
    @29
    cD
    @43
    nn0cnd
    nncand
    fveq2d
    @29
    @19
    @22
    @23
    @75
    cC
    wceq
    @35
    wph
    @22
    @28
    coe1tmmul.c
    adantr
    @43
    cC
    cD
    cP
    cR
    c.x
    c.ex
    cK
    cN
    cX
    c.0
    coe1tm.z
    coe1tm.k
    coe1tm.p
    coe1tm.x
    coe1tm.m
    coe1tm.n
    coe1tm.e
    coe1tmfv1
    syl3anc
    eqtrd
    oveq2d
    3eqtrd
    anassrs
    @27
    @14
    wn
    #
    wa
    #
    @12
    cR
    vy
    @3
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @77
    @11
    @78
    cR
    cgsu
    @77
    vy
    @3
    @10
    c.0
    @27
    @76
    @50
    @10
    c.0
    wceq
    @27
    @76
    @50
    wa
    #
    wa
    #
    @10
    @66
    c.0
    @81
    @9
    c.0
    @6
    c.xp
    @81
    cC
    cD
    cP
    cR
    c.x
    c.ex
    @7
    cK
    cN
    cX
    c.0
    coe1tm.z
    coe1tm.k
    coe1tm.p
    coe1tm.x
    coe1tm.m
    coe1tm.n
    coe1tm.e
    wph
    @19
    @26
    @80
    coe1tmmul.r
    ad2antrr
    #
    wph
    @22
    @26
    @80
    coe1tmmul.c
    ad2antrr
    wph
    @23
    @26
    @80
    coe1tmmul.d
    ad2antrr
    @50
    @60
    @27
    @76
    @61
    ad2antll
    @81
    @7
    cD
    @50
    @7
    cr
    wcel
    @27
    @76
    @50
    @7
    @61
    nn0red
    ad2antll
    #
    @81
    @7
    @2
    cD
    @83
    @26
    @45
    wph
    @80
    @46
    ad2antlr
    #
    wph
    @47
    @26
    @80
    @48
    ad2antrr
    #
    @81
    cc0
    @4
    cle
    wbr
    @7
    @2
    cle
    wbr
    @81
    @4
    @50
    @56
    @27
    @76
    @57
    ad2antll
    #
    nn0ge0d
    @81
    @2
    @4
    @84
    @50
    @4
    cr
    wcel
    @27
    @76
    @50
    @4
    @57
    nn0red
    ad2antll
    subge02d
    mpbid
    @81
    @2
    cD
    clt
    wbr
    @76
    @27
    @76
    @50
    simprl
    @81
    @2
    cD
    @84
    @85
    ltnled
    mpbird
    lelttrd
    gtned
    coe1tmfv2
    oveq2d
    @81
    @19
    @52
    @73
    @82
    @81
    cn0
    cK
    @4
    @5
    wph
    @54
    @26
    @80
    @55
    ad2antrr
    @86
    ffvelrnd
    @74
    syl2anc
    eqtrd
    anassrs
    mpteq2dva
    oveq2d
    wph
    @79
    c.0
    wceq
    #
    @26
    @76
    wph
    @34
    @37
    @87
    wph
    @19
    @34
    coe1tmmul.r
    @36
    syl
    @38
    @3
    vy
    cR
    cvv
    c.0
    coe1tm.z
    gsumz
    sylancl
    ad2antrr
    eqtrd
    ifbothda
    mpteq2dva
    eqtrd
end
