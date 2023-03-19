include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cc0.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "cfz.mm"
include "cplusg.mm"
include "simpr.mm"
include "c0g.mm"
include "cmnd.mm"
include "pmatring.mm"
include "ringmnd.mm"
include "syl.mm"
include "adantr.mm"
include "ccmn.mm"
include "ringcmn.mm"
include "snfi.mm"
include "a1i.mm"
include "cn0.mm"
include "simplll.mm"
include "simpllr.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "elsni.mm"
include "0nn0.mm"
include "syl6eqel.mm"
include "mat2pmatscmxcl.mm"
include "syl22anc.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "eqid.mm"
include "mndrid.mm"
include "syl2anc.mm"
include "cz.mm"
include "0z.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cif.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "iftrued.mm"
include "fveq2.mm"
include "eqcomd.mm"
include "cuz.mm"
include "1nn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "eleq1.mm"
include "mpbird.mm"
include "wi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "imp.mm"
include "fvmptd.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq12dva.mm"
include "cvv.mm"
include "ovexd.mm"
include "mndidcl.mm"
include "wn.mm"
include "0p1e1.mm"
include "eqeq2i.mm"
include "ax-1ne0.mm"
include "neii.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "sylbi.mm"
include "wb.mm"
include "notbid.mm"
include "iffalsed.mm"
include "syl6eq.mm"
include "eluzfz2.mm"
include "fvexd.mm"
include "cmat.mm"
include "fveq2i.mm"
include "0mat2pmat.mm"
include "ancoms.mm"
include "ad2antrr.mm"
include "clmod.mm"
include "csca.mm"
include "cbs.mm"
include "pmatlmod.mm"
include "cmgp.mm"
include "ply1moncl.mm"
include "ply1ring.mm"
include "matsca2.mm"
include "sylan2.mm"
include "eleq2d.mm"
include "lmodvs0.mm"
include "gsumsnd.mm"
include "oveq12d.mm"
include "eqtr3d.mm"
include "3impa.mm"
include "id.mm"
include "c0ex.mm"
include "snid.mm"
include "ffvelrnd.mm"
include "matring.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "fmptd.mm"
include "oveq2i.mm"
include "feq2i.mm"
include "sylibr.mm"
include "elfznn0.mm"
include "gsummptfzsplit.mm"
include "3adant3.mm"
include "eqtr4d.mm"
include "mpteq1.mm"

theorem pmatcollpw3fi1lem1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cH: class H
  let c.as: class .*
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vl: setvar l
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let cI: class I
  assume pmatcollpw.p: |- P = ( Poly1 ` R )
  assume pmatcollpw.c: |- C = ( N Mat P )
  assume pmatcollpw.b: |- B = ( Base ` C )
  assume pmatcollpw.m: |- .* = ( .s ` C )
  assume pmatcollpw.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpw.x: |- X = ( var1 ` R )
  assume pmatcollpw.t: |- T = ( N matToPolyMat R )
  assume pmatcollpw3.a: |- A = ( N Mat R )
  assume pmatcollpw3.d: |- D = ( Base ` A )
  assume pmatcollpw3fi1lem1.0: |- .0. = ( 0g ` A )
  assume pmatcollpw3fi1lem1.h: |- H = ( l e. ( 0 ... 1 ) |-> if ( l = 0 , ( G ` 0 ) , .0. ) )

  disjoint A l
  disjoint G l
  disjoint G n
  disjoint l n
  disjoint B n
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint R n
  disjoint X n
  disjoint .^ n
  disjoint C n
  disjoint B l
  disjoint M l
  disjoint N l
  disjoint R l
  disjoint D l
  disjoint D n
  disjoint l n
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint i n
  disjoint j n
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a n
  disjoint b n
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint P a
  disjoint P b
  disjoint R a
  disjoint R b
  disjoint T a
  disjoint T b
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint .* a
  disjoint .* b
  disjoint .^ a
  disjoint .^ b
  disjoint .^ i
  disjoint .^ j
  disjoint B s
  disjoint n s
  disjoint M s
  disjoint N s
  disjoint R s
  disjoint B f
  disjoint f i
  disjoint f j
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint B m
  disjoint C f
  disjoint f n
  disjoint f x
  disjoint n x
  disjoint D f
  disjoint D k
  disjoint f k
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint I l
  disjoint I x
  disjoint I y
  disjoint i k
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j l
  disjoint j x
  disjoint j y
  disjoint I f
  disjoint I n
  disjoint k n
  disjoint M k
  disjoint M x
  disjoint M y
  disjoint M f
  disjoint M m
  disjoint i m
  disjoint j m
  disjoint k m
  disjoint N f
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint N m
  disjoint R f
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint R m
  disjoint T f
  disjoint X f
  disjoint .^ f
  disjoint .* f
  disjoint f s
  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ G e. ( D ^m { 0 } ) /\ M = ( C gsum ( n e. { 0 } |-> ( ( n .^ X ) .* ( T ` ( G ` n ) ) ) ) ) ) -> M = ( C gsum ( n e. ( 0 ... 1 ) |-> ( ( n .^ X ) .* ( T ` ( H ` n ) ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cG
    cD
    cc0
    csn
    #
    cmap
    co
    wcel
    #
    cM
    cC
    vn
    @3
    vn
    cv
    #
    cX
    c.ex
    co
    #
    @5
    cG
    cfv
    #
    cT
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
    wceq
    #
    w3a
    #
    cM
    cC
    vn
    cc0
    cc0
    c1
    caddc
    co
    #
    cfz
    co
    #
    @6
    @5
    cH
    cfv
    #
    cT
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
    cC
    vn
    cc0
    c1
    cfz
    co
    #
    @18
    cmpt
    #
    cgsu
    co
    @13
    cM
    cC
    vn
    cc0
    cc0
    cfz
    co
    #
    @18
    cmpt
    #
    cgsu
    co
    #
    cC
    vn
    @14
    csn
    @18
    cmpt
    cgsu
    co
    #
    cC
    cplusg
    cfv
    #
    co
    #
    @20
    @2
    @4
    @12
    cM
    @28
    wceq
    @2
    @4
    wa
    #
    @12
    wa
    cM
    @11
    @28
    @29
    @12
    simpr
    @29
    @11
    @28
    wceq
    @12
    @29
    @11
    cC
    c0g
    cfv
    #
    @27
    co
    #
    @11
    @28
    @29
    cC
    cmnd
    wcel
    #
    @11
    cB
    wcel
    @31
    @11
    wceq
    @2
    @32
    @4
    @2
    cC
    crg
    wcel
    #
    @32
    cC
    cP
    cR
    cN
    pmatcollpw.p
    pmatcollpw.c
    pmatring
    #
    cC
    ringmnd
    syl
    #
    adantr
    #
    @29
    cB
    vn
    cC
    @3
    @9
    pmatcollpw.b
    @2
    cC
    ccmn
    wcel
    #
    @4
    @2
    @33
    @37
    @34
    cC
    ringcmn
    syl
    adantr
    #
    @3
    cfn
    wcel
    @29
    cc0
    snfi
    a1i
    @29
    @9
    cB
    wcel
    #
    vn
    @3
    @29
    @5
    @3
    wcel
    #
    wa
    #
    @0
    @1
    @7
    cD
    wcel
    #
    @5
    cn0
    wcel
    #
    @39
    @0
    @1
    @4
    @40
    simplll
    @0
    @1
    @4
    @40
    simpllr
    @29
    @3
    cD
    @5
    cG
    @4
    @3
    cD
    cG
    wf
    #
    @2
    cG
    cD
    @3
    elmapi
    #
    adantl
    ffvelrnda
    @40
    @43
    @29
    @40
    @5
    cc0
    cn0
    @5
    cc0
    elsni
    #
    0nn0
    syl6eqel
    adantl
    cA
    cB
    cC
    cP
    cR
    cT
    c.ex
    c.as
    cD
    @5
    @7
    cN
    cX
    pmatcollpw3.a
    pmatcollpw3.d
    pmatcollpw.t
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    pmatcollpw.m
    pmatcollpw.e
    pmatcollpw.x
    mat2pmatscmxcl
    syl22anc
    ralrimiva
    gsummptcl
    cB
    @27
    cC
    @11
    @30
    pmatcollpw.b
    @27
    eqid
    #
    @30
    eqid
    #
    mndrid
    syl2anc
    @29
    @11
    @25
    @30
    @26
    @27
    @29
    @10
    @24
    cC
    cgsu
    @29
    vn
    @3
    @9
    @23
    @18
    @3
    @23
    wceq
    @29
    @23
    @3
    cc0
    cz
    wcel
    @23
    @3
    wceq
    0z
    cc0
    fzsn
    ax-mp
    eqcomi
    a1i
    @41
    @8
    @17
    @6
    c.as
    @41
    @7
    @16
    cT
    @41
    @16
    @7
    @41
    vl
    @5
    vl
    cv
    #
    cc0
    wceq
    #
    cc0
    cG
    cfv
    #
    c.0
    cif
    #
    @7
    @21
    cH
    cD
    cH
    vl
    @21
    @52
    cmpt
    wceq
    #
    @41
    pmatcollpw3fi1lem1.h
    a1i
    @41
    @49
    @5
    wceq
    #
    wa
    #
    @52
    @51
    @7
    @55
    @50
    @51
    c.0
    @55
    @49
    @5
    cc0
    @41
    @54
    simpr
    @40
    @5
    cc0
    wceq
    #
    @29
    @54
    @46
    ad2antlr
    eqtrd
    iftrued
    @40
    @51
    @7
    wceq
    #
    @29
    @54
    @40
    @56
    @57
    @46
    @56
    @7
    @51
    @5
    cc0
    cG
    fveq2
    eqcomd
    syl
    ad2antlr
    eqtrd
    @40
    @5
    @21
    wcel
    #
    @29
    @40
    @56
    @58
    @46
    @56
    @58
    cc0
    @21
    wcel
    #
    @56
    c1
    cc0
    cuz
    cfv
    #
    wcel
    #
    @59
    @56
    c1
    cn0
    @60
    c1
    cn0
    wcel
    #
    @56
    1nn0
    a1i
    nn0uz
    syl6eleq
    cc0
    c1
    eluzfz1
    syl
    @5
    cc0
    @21
    eleq1
    mpbird
    syl
    adantl
    @29
    @40
    @42
    @4
    @40
    @42
    wi
    #
    @2
    @4
    @44
    @63
    @45
    @44
    @40
    @42
    @3
    cD
    @5
    cG
    ffvelrn
    ex
    syl
    adantl
    imp
    fvmptd
    eqcomd
    fveq2d
    oveq2d
    mpteq12dva
    oveq2d
    @29
    @26
    @30
    @29
    @18
    cB
    @30
    vn
    cC
    @14
    cvv
    pmatcollpw.b
    @36
    @29
    cc0
    c1
    caddc
    ovexd
    @2
    @30
    cB
    wcel
    #
    @4
    @2
    @32
    @64
    @35
    cB
    cC
    @30
    pmatcollpw.b
    @48
    mndidcl
    syl
    adantr
    @29
    @5
    @14
    wceq
    #
    wa
    #
    @18
    @6
    @30
    c.as
    co
    #
    @30
    @66
    @17
    @30
    @6
    c.as
    @66
    @17
    cA
    c0g
    cfv
    #
    cT
    cfv
    #
    @30
    @66
    @16
    @68
    cT
    @66
    vl
    @5
    @52
    @68
    @21
    cH
    cvv
    @53
    @66
    pmatcollpw3fi1lem1.h
    a1i
    @66
    @54
    wa
    #
    @52
    c.0
    @68
    @70
    @50
    @51
    c.0
    @70
    @50
    wn
    #
    @56
    wn
    #
    @65
    @72
    @29
    @54
    @65
    @5
    c1
    wceq
    #
    @72
    @14
    c1
    @5
    0p1e1
    eqeq2i
    #
    @73
    @56
    c1
    cc0
    wceq
    c1
    cc0
    ax-1ne0
    neii
    @5
    c1
    cc0
    eqeq1
    mtbiri
    sylbi
    ad2antlr
    @54
    @71
    @72
    wb
    @66
    @54
    @50
    @56
    @49
    @5
    cc0
    eqeq1
    notbid
    adantl
    mpbird
    iffalsed
    pmatcollpw3fi1lem1.0
    syl6eq
    @65
    @58
    @29
    @65
    @73
    @58
    @74
    @73
    @58
    c1
    @21
    wcel
    #
    @73
    @61
    @75
    @73
    c1
    cn0
    @60
    @62
    @73
    1nn0
    a1i
    #
    nn0uz
    syl6eleq
    cc0
    c1
    eluzfz2
    syl
    @5
    c1
    @21
    eleq1
    mpbird
    sylbi
    adantl
    @66
    cA
    c0g
    fvexd
    fvmptd
    fveq2d
    @2
    @69
    @30
    wceq
    #
    @4
    @65
    @1
    @0
    @77
    cP
    cR
    cT
    cN
    @68
    @30
    pmatcollpw.t
    pmatcollpw.p
    cA
    cN
    cR
    cmat
    co
    c0g
    pmatcollpw3.a
    fveq2i
    cC
    cN
    cP
    cmat
    co
    c0g
    pmatcollpw.c
    fveq2i
    0mat2pmat
    ancoms
    ad2antrr
    eqtrd
    oveq2d
    @66
    cC
    clmod
    wcel
    #
    @6
    cC
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @67
    @30
    wceq
    @2
    @78
    @4
    @65
    cC
    cP
    cR
    cN
    pmatcollpw.p
    pmatcollpw.c
    pmatlmod
    ad2antrr
    @66
    @81
    @6
    cP
    cbs
    cfv
    #
    wcel
    #
    @66
    @1
    @43
    @83
    @0
    @1
    @4
    @65
    simpllr
    @65
    @43
    @29
    @65
    @73
    @43
    @74
    @73
    @43
    @62
    @76
    @5
    c1
    cn0
    eleq1
    mpbird
    sylbi
    adantl
    @82
    @5
    cP
    cR
    c.ex
    cP
    cmgp
    cfv
    #
    cX
    pmatcollpw.p
    pmatcollpw.x
    @84
    eqid
    pmatcollpw.e
    @82
    eqid
    ply1moncl
    syl2anc
    @2
    @81
    @83
    wb
    @4
    @65
    @2
    @80
    @82
    @6
    @2
    @79
    cP
    cbs
    @2
    cP
    @79
    @1
    @0
    cP
    crg
    wcel
    cP
    @79
    wceq
    cP
    cR
    pmatcollpw.p
    ply1ring
    cC
    cP
    cN
    crg
    pmatcollpw.c
    matsca2
    sylan2
    eqcomd
    fveq2d
    eleq2d
    ad2antrr
    mpbird
    c.as
    @79
    @80
    cC
    @6
    @30
    @79
    eqid
    pmatcollpw.m
    @80
    eqid
    @48
    lmodvs0
    syl2anc
    eqtrd
    gsumsnd
    eqcomd
    oveq12d
    eqtr3d
    adantr
    eqtrd
    3impa
    @2
    @4
    @20
    @28
    wceq
    @12
    @29
    cB
    @27
    vn
    cC
    cc0
    @18
    pmatcollpw.b
    @47
    @38
    cc0
    cn0
    wcel
    @29
    0nn0
    a1i
    @29
    @5
    @15
    wcel
    #
    wa
    @0
    @1
    @16
    cD
    wcel
    @43
    @18
    cB
    wcel
    @0
    @1
    @4
    @85
    simplll
    @0
    @1
    @4
    @85
    simpllr
    @29
    @15
    cD
    @5
    cH
    @29
    @21
    cD
    cH
    wf
    @15
    cD
    cH
    wf
    @29
    vl
    @21
    @52
    cD
    cH
    @29
    @49
    @21
    wcel
    #
    wa
    @50
    @51
    c.0
    cD
    @4
    @51
    cD
    wcel
    #
    @2
    @86
    @4
    @44
    @87
    @45
    @44
    @3
    cD
    cc0
    cG
    @44
    id
    cc0
    @3
    wcel
    @44
    cc0
    c0ex
    snid
    a1i
    ffvelrnd
    syl
    ad2antlr
    @2
    c.0
    cD
    wcel
    #
    @4
    @86
    @2
    cA
    crg
    wcel
    @88
    cA
    cR
    cN
    pmatcollpw3.a
    matring
    cD
    cA
    c.0
    pmatcollpw3.d
    pmatcollpw3fi1lem1.0
    ring0cl
    syl
    ad2antrr
    ifcld
    pmatcollpw3fi1lem1.h
    fmptd
    @15
    @21
    cD
    cH
    @14
    c1
    cc0
    cfz
    0p1e1
    oveq2i
    #
    feq2i
    sylibr
    ffvelrnda
    @85
    @43
    @29
    @5
    @14
    elfznn0
    adantl
    cA
    cB
    cC
    cP
    cR
    cT
    c.ex
    c.as
    cD
    @5
    @16
    cN
    cX
    pmatcollpw3.a
    pmatcollpw3.d
    pmatcollpw.t
    pmatcollpw.p
    pmatcollpw.c
    pmatcollpw.b
    pmatcollpw.m
    pmatcollpw.e
    pmatcollpw.x
    mat2pmatscmxcl
    syl22anc
    gsummptfzsplit
    3adant3
    eqtr4d
    @19
    @22
    cC
    cgsu
    @15
    @21
    wceq
    @19
    @22
    wceq
    @89
    vn
    @15
    @21
    @18
    mpteq1
    ax-mp
    oveq2i
    syl6eq
end
