include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cn0.mm"
include "cc0.mm"
include "cfz.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "coe1mul.mm"
include "adantr.mm"
include "fveq1d.mm"
include "cvv.mm"
include "eqidd.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "simpr.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "csb.mm"
include "cbs.mm"
include "c0g.mm"
include "cmg.mm"
include "cmgp.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "simp1.mm"
include "eqid.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "fzfid.mm"
include "simpll1.mm"
include "simp2.mm"
include "elfznn0.mm"
include "coe1fvalcl.mm"
include "syl2an.mm"
include "simp3.mm"
include "fznn0sub.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "cfsupp.mm"
include "wbr.mm"
include "ply1mulgsumlem3.mm"
include "gsummoncoe1.mm"
include "vex.mm"
include "csbov2g.mm"
include "id.mm"
include "csbied.mm"
include "eqtrd.mm"
include "mp1i.mm"
include "fveq2.mm"
include "fveq1i.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "a1i.mm"
include "3eqtrrd.mm"
include "3eqtrd.mm"
include "wb.mm"
include "ply1ring.mm"
include "syl3an1.mm"
include "syl.mm"
include "nn0ex.mm"
include "clmod.mm"
include "csca.mm"
include "ply1lmod.mm"
include "ply1sca.mm"
include "eleqtrd.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "lmodvscl.mm"
include "fmptd.mm"
include "ply1mulgsumlem4.mm"
include "gsumcl.mm"
include "ply1coe1eq.mm"
include "mpbid.mm"

theorem ply1mulgsum
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vk: setvar k
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let vl: setvar l
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  let vz: setvar z
  let vi: setvar i
  let vm: setvar m
  assume ply1mulgsum.p: |- P = ( Poly1 ` R )
  assume ply1mulgsum.b: |- B = ( Base ` P )
  assume ply1mulgsum.a: |- A = ( coe1 ` K )
  assume ply1mulgsum.c: |- C = ( coe1 ` L )
  assume ply1mulgsum.x: |- X = ( var1 ` R )
  assume ply1mulgsum.pm: |- .X. = ( .r ` P )
  assume ply1mulgsum.sm: |- .x. = ( .s ` P )
  assume ply1mulgsum.rm: |- .* = ( .r ` R )
  assume ply1mulgsum.m: |- M = ( mulGrp ` P )
  assume ply1mulgsum.e: |- .^ = ( .g ` M )

  disjoint A l
  disjoint B l
  disjoint C l
  disjoint K l
  disjoint L l
  disjoint R l
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint K k
  disjoint L k
  disjoint R k
  disjoint .* k
  disjoint k l
  disjoint X k
  disjoint .^ k
  disjoint .x. k
  disjoint P k
  disjoint .* l
  disjoint A a
  disjoint A b
  disjoint A n
  disjoint A s
  disjoint a b
  disjoint a n
  disjoint a s
  disjoint b n
  disjoint b s
  disjoint n s
  disjoint B a
  disjoint B b
  disjoint B n
  disjoint B s
  disjoint C a
  disjoint C b
  disjoint C n
  disjoint C s
  disjoint K a
  disjoint K b
  disjoint K n
  disjoint K s
  disjoint L a
  disjoint L b
  disjoint L n
  disjoint L s
  disjoint R a
  disjoint R b
  disjoint R n
  disjoint R s
  disjoint A x
  disjoint A z
  disjoint l n
  disjoint l x
  disjoint l z
  disjoint n x
  disjoint n z
  disjoint x z
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint K x
  disjoint K z
  disjoint L x
  disjoint L z
  disjoint R x
  disjoint R z
  disjoint l s
  disjoint s x
  disjoint s z
  disjoint .* s
  disjoint .* z
  disjoint .* n
  disjoint k n
  disjoint k s
  disjoint P n
  disjoint P s
  disjoint X n
  disjoint X s
  disjoint .^ n
  disjoint .^ s
  disjoint .x. n
  disjoint .x. s
  disjoint A i
  disjoint B m
  disjoint C i
  disjoint K i
  disjoint K m
  disjoint i m
  disjoint i n
  disjoint m n
  disjoint L i
  disjoint L m
  disjoint R i
  disjoint R m
  disjoint .X. m
  disjoint .X. n
  disjoint .* i
  disjoint .* m
  disjoint i l
  disjoint l m
  disjoint k x
  assert |- ( ( R e. Ring /\ K e. B /\ L e. B ) -> ( K .X. L ) = ( P gsum ( k e. NN0 |-> ( ( R gsum ( l e. ( 0 ... k ) |-> ( ( A ` l ) .* ( C ` ( k - l ) ) ) ) ) .x. ( k .^ X ) ) ) ) )

  proof
    cR
    crg
    wcel
    #
    cK
    cB
    wcel
    #
    cL
    cB
    wcel
    #
    w3a
    #
    vn
    cv
    #
    cK
    cL
    c.xp
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @4
    cP
    vk
    cn0
    cR
    vl
    cc0
    vk
    cv
    #
    cfz
    co
    #
    vl
    cv
    #
    cA
    cfv
    #
    @8
    @10
    cmin
    co
    #
    cC
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @8
    cX
    c.ex
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    wceq
    #
    vn
    cn0
    wral
    #
    @5
    @20
    wceq
    #
    @3
    @23
    vn
    cn0
    @3
    @4
    cn0
    wcel
    #
    wa
    #
    @7
    @4
    vm
    cn0
    cR
    vi
    cc0
    vm
    cv
    #
    cfz
    co
    #
    vi
    cv
    #
    cK
    cco1
    cfv
    #
    cfv
    #
    @28
    @30
    cmin
    co
    #
    cL
    cco1
    cfv
    #
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cfv
    cR
    vi
    cc0
    @4
    cfz
    co
    #
    @32
    @4
    @30
    cmin
    co
    #
    @34
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @22
    @27
    @4
    @6
    @39
    @3
    @6
    @39
    wceq
    @26
    vi
    cB
    cR
    c.xp
    c.as
    vm
    cK
    cL
    cP
    ply1mulgsum.p
    ply1mulgsum.pm
    ply1mulgsum.rm
    ply1mulgsum.b
    coe1mul
    adantr
    fveq1d
    @27
    vm
    @4
    @38
    @45
    cn0
    @39
    cvv
    @27
    @39
    eqidd
    vm
    vn
    weq
    #
    @38
    @45
    wceq
    @27
    @46
    @37
    @44
    cR
    cgsu
    @46
    vi
    @29
    @36
    @40
    @43
    @28
    @4
    cc0
    cfz
    oveq2
    @46
    @35
    @42
    @32
    c.as
    @46
    @33
    @41
    @34
    @28
    @4
    @30
    cmin
    oveq1
    fveq2d
    oveq2d
    mpteq12dv
    oveq2d
    adantl
    @3
    @26
    simpr
    #
    @27
    cR
    @44
    cgsu
    ovexd
    fvmptd
    @27
    @22
    vk
    @4
    @16
    csb
    #
    cR
    vl
    @40
    @11
    @4
    @10
    cmin
    co
    #
    cC
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @45
    @27
    @16
    cB
    cP
    cR
    vk
    c.ex
    c.x
    cR
    cbs
    cfv
    #
    @4
    cX
    cR
    c0g
    cfv
    #
    ply1mulgsum.p
    ply1mulgsum.b
    ply1mulgsum.x
    c.ex
    cM
    cmg
    cfv
    cP
    cmgp
    cfv
    #
    cmg
    cfv
    ply1mulgsum.e
    cM
    @56
    cmg
    ply1mulgsum.m
    fveq2i
    eqtri
    @3
    @0
    @26
    @0
    @1
    @2
    simp1
    #
    adantr
    @54
    eqid
    #
    ply1mulgsum.sm
    @55
    eqid
    @27
    @16
    @54
    wcel
    vk
    cn0
    @27
    @8
    cn0
    wcel
    #
    wa
    #
    @54
    vl
    cR
    @9
    @14
    @58
    @3
    cR
    ccmn
    wcel
    #
    @26
    @59
    @0
    @1
    @61
    @2
    cR
    ringcmn
    3ad2ant1
    #
    ad2antrr
    @60
    cc0
    @8
    fzfid
    @60
    @14
    @54
    wcel
    #
    vl
    @9
    @60
    @10
    @9
    wcel
    #
    wa
    @0
    @11
    @54
    wcel
    #
    @13
    @54
    wcel
    #
    @63
    @60
    @0
    @64
    @0
    @1
    @2
    @26
    @59
    simpll1
    adantr
    @60
    @1
    @10
    cn0
    wcel
    #
    @65
    @64
    @3
    @1
    @26
    @59
    @0
    @1
    @2
    simp2
    #
    ad2antrr
    @10
    @8
    elfznn0
    #
    cA
    cB
    cP
    cR
    cK
    @54
    @10
    ply1mulgsum.a
    ply1mulgsum.b
    ply1mulgsum.p
    @58
    coe1fvalcl
    #
    syl2an
    @60
    @2
    @12
    cn0
    wcel
    #
    @66
    @64
    @3
    @2
    @26
    @59
    @0
    @1
    @2
    simp3
    #
    ad2antrr
    @10
    cc0
    @8
    fznn0sub
    #
    cC
    cB
    cP
    cR
    cL
    @54
    @12
    ply1mulgsum.c
    ply1mulgsum.b
    ply1mulgsum.p
    @58
    coe1fvalcl
    #
    syl2an
    @54
    cR
    c.as
    @11
    @13
    @58
    ply1mulgsum.rm
    ringcl
    #
    syl3anc
    ralrimiva
    gsummptcl
    ralrimiva
    @3
    vk
    cn0
    @16
    cmpt
    @55
    cfsupp
    wbr
    @26
    cA
    cB
    cC
    cP
    cR
    c.x
    c.xp
    vk
    c.ex
    c.as
    cK
    cL
    cM
    cX
    vl
    ply1mulgsum.p
    ply1mulgsum.b
    ply1mulgsum.a
    ply1mulgsum.c
    ply1mulgsum.x
    ply1mulgsum.pm
    ply1mulgsum.sm
    ply1mulgsum.rm
    ply1mulgsum.m
    ply1mulgsum.e
    ply1mulgsumlem3
    adantr
    @47
    gsummoncoe1
    @4
    cvv
    wcel
    #
    @48
    @53
    wceq
    @27
    vn
    vex
    @76
    @48
    cR
    vk
    @4
    @15
    csb
    #
    cgsu
    co
    @53
    vk
    @4
    cR
    @15
    cgsu
    cvv
    csbov2g
    @76
    @77
    @52
    cR
    cgsu
    @76
    vk
    @4
    @15
    @52
    cvv
    @76
    id
    vk
    vn
    weq
    #
    @15
    @52
    wceq
    @76
    @78
    vl
    @9
    @14
    @40
    @51
    @8
    @4
    cc0
    cfz
    oveq2
    @78
    @13
    @50
    @11
    c.as
    @78
    @12
    @49
    cC
    @8
    @4
    @10
    cmin
    oveq1
    fveq2d
    oveq2d
    mpteq12dv
    adantl
    csbied
    oveq2d
    eqtrd
    mp1i
    @27
    @52
    @44
    cR
    cgsu
    @52
    @44
    wceq
    @27
    vl
    vi
    @40
    @51
    @43
    vl
    vi
    weq
    #
    @11
    @32
    @50
    @42
    c.as
    @79
    @11
    @30
    cA
    cfv
    @32
    @10
    @30
    cA
    fveq2
    @30
    cA
    @31
    ply1mulgsum.a
    fveq1i
    syl6eq
    @79
    @50
    @41
    cC
    cfv
    @42
    @79
    @49
    @41
    cC
    @10
    @30
    @4
    cmin
    oveq2
    fveq2d
    @41
    cC
    @34
    ply1mulgsum.c
    fveq1i
    syl6eq
    oveq12d
    cbvmptv
    a1i
    oveq2d
    3eqtrrd
    3eqtrd
    ralrimiva
    @3
    @0
    @5
    cB
    wcel
    #
    @20
    cB
    wcel
    @24
    @25
    wb
    @57
    @0
    cP
    crg
    wcel
    #
    @1
    @2
    @80
    cP
    cR
    ply1mulgsum.p
    ply1ring
    #
    cB
    cP
    c.xp
    cK
    cL
    ply1mulgsum.b
    ply1mulgsum.pm
    ringcl
    syl3an1
    @3
    cn0
    cB
    @19
    cP
    cvv
    cP
    c0g
    cfv
    #
    ply1mulgsum.b
    @83
    eqid
    @0
    @1
    cP
    ccmn
    wcel
    #
    @2
    @0
    @81
    @84
    @82
    cP
    ringcmn
    syl
    3ad2ant1
    cn0
    cvv
    wcel
    @3
    nn0ex
    a1i
    @3
    vk
    cn0
    @18
    cB
    @19
    @3
    @59
    wa
    #
    cP
    clmod
    wcel
    #
    @16
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @17
    cB
    wcel
    #
    @18
    cB
    wcel
    @3
    @86
    @59
    @0
    @1
    @86
    @2
    cP
    cR
    ply1mulgsum.p
    ply1lmod
    3ad2ant1
    adantr
    @85
    @16
    @54
    @88
    @85
    @54
    vl
    cR
    @9
    @14
    @58
    @3
    @61
    @59
    @62
    adantr
    @85
    cc0
    @8
    fzfid
    @85
    @63
    vl
    @9
    @85
    @64
    wa
    @0
    @65
    @66
    @63
    @0
    @1
    @2
    @59
    @64
    simpll1
    @85
    @1
    @67
    @65
    @64
    @3
    @1
    @59
    @68
    adantr
    @69
    @70
    syl2an
    @85
    @2
    @71
    @66
    @64
    @3
    @2
    @59
    @72
    adantr
    @73
    @74
    syl2an
    @75
    syl3anc
    ralrimiva
    gsummptcl
    @85
    cR
    @87
    cbs
    @85
    @0
    cR
    @87
    wceq
    @3
    @0
    @59
    @57
    adantr
    cP
    cR
    crg
    ply1mulgsum.p
    ply1sca
    syl
    fveq2d
    eleqtrd
    @85
    cM
    cmnd
    wcel
    #
    @59
    cX
    cB
    wcel
    #
    @89
    @3
    @90
    @59
    @0
    @1
    @90
    @2
    @0
    @81
    @90
    @82
    cP
    cM
    ply1mulgsum.m
    ringmgp
    syl
    3ad2ant1
    adantr
    @3
    @59
    simpr
    @3
    @91
    @59
    @0
    @1
    @91
    @2
    cB
    cP
    cR
    cX
    ply1mulgsum.x
    ply1mulgsum.p
    ply1mulgsum.b
    vr1cl
    3ad2ant1
    adantr
    cB
    c.ex
    cM
    @8
    cX
    cB
    cP
    cM
    ply1mulgsum.m
    ply1mulgsum.b
    mgpbas
    ply1mulgsum.e
    mulgnn0cl
    syl3anc
    @16
    c.x
    @87
    @88
    cB
    cP
    @17
    ply1mulgsum.b
    @87
    eqid
    ply1mulgsum.sm
    @88
    eqid
    lmodvscl
    syl3anc
    @19
    eqid
    fmptd
    cA
    cB
    cC
    cP
    cR
    c.x
    c.xp
    vk
    c.ex
    c.as
    cK
    cL
    cM
    cX
    vl
    ply1mulgsum.p
    ply1mulgsum.b
    ply1mulgsum.a
    ply1mulgsum.c
    ply1mulgsum.x
    ply1mulgsum.pm
    ply1mulgsum.sm
    ply1mulgsum.rm
    ply1mulgsum.m
    ply1mulgsum.e
    ply1mulgsumlem4
    gsumcl
    @6
    cB
    @21
    cP
    cR
    vn
    @5
    @20
    ply1mulgsum.p
    ply1mulgsum.b
    @6
    eqid
    @21
    eqid
    ply1coe1eq
    syl3anc
    mpbid
end
