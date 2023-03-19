include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cn.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wa.mm"
include "c2.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "wceq.mm"
include "cn0.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "cz.mm"
include "cle.mm"
include "eluz2.mm"
include "simpll.mm"
include "nngt0.mm"
include "cr.mm"
include "nnre.mm"
include "adantl.mm"
include "crp.mm"
include "2rp.mm"
include "a1i.mm"
include "ltaddrpd.mm"
include "0red.mm"
include "2re.mm"
include "readdcld.mm"
include "lttr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "ex.mm"
include "com13.mm"
include "mpcom.mm"
include "impcom.mm"
include "zre.mm"
include "adantr.mm"
include "ltleletr.mm"
include "mpand.mm"
include "imp.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "cc.mm"
include "nncn.mm"
include "add1p1.mm"
include "syl.mm"
include "eqcomd.mm"
include "breq1d.mm"
include "wb.mm"
include "nnz.mm"
include "peano2zd.mm"
include "anim2i.mm"
include "ancomd.mm"
include "zltp1le.mm"
include "bicomd.mm"
include "bitrd.mm"
include "biimpa.mm"
include "jca.mm"
include "impancom.mm"
include "3adant1.mm"
include "com12.mm"
include "syl5bi.mm"
include "cmin.mm"
include "cif.mm"
include "cvv.mm"
include "cmpt.mm"
include "wn.mm"
include "peano2re.mm"
include "ad2antrr.mm"
include "nn0re.mm"
include "ad2antlr.mm"
include "nnnn0.mm"
include "nn0p1gt0.mm"
include "simpr.mm"
include "lttrd.mm"
include "gt0ne0d.mm"
include "neneqd.mm"
include "eqeq1.mm"
include "notbid.mm"
include "mpbird.mm"
include "iffalsed.mm"
include "wne.mm"
include "ltne.mm"
include "sylan.mm"
include "simplr.mm"
include "breq2.mm"
include "iftrued.mm"
include "3eqtrd.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvmptd.mm"
include "oveq2d.mm"
include "clmod.mm"
include "csca.mm"
include "cbs.mm"
include "crg.mm"
include "crngring.mm"
include "pmatlmod.mm"
include "sylan2.mm"
include "3adant3.mm"
include "cmgp.mm"
include "cmnd.mm"
include "ply1ring.mm"
include "3ad2ant2.mm"
include "eqid.mm"
include "ringmgp.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "ply1crng.mm"
include "matsca2.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "lmodvs0.mm"
include "eqtrd.mm"
include "expl.mm"
include "syld.mm"
include "3impia.mm"

theorem chfacfscmul0
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  let vk: setvar k
  let vl: setvar l
  assume chfacfisf.a: |- A = ( N Mat R )
  assume chfacfisf.b: |- B = ( Base ` A )
  assume chfacfisf.p: |- P = ( Poly1 ` R )
  assume chfacfisf.y: |- Y = ( N Mat P )
  assume chfacfisf.r: |- .X. = ( .r ` Y )
  assume chfacfisf.s: |- .- = ( -g ` Y )
  assume chfacfisf.0: |- .0. = ( 0g ` Y )
  assume chfacfisf.t: |- T = ( N matToPolyMat R )
  assume chfacfisf.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume chfacfscmulcl.x: |- X = ( var1 ` R )
  assume chfacfscmulcl.m: |- .x. = ( .s ` Y )
  assume chfacfscmulcl.e: |- .^ = ( .g ` ( mulGrp ` P ) )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint Y n
  disjoint b n
  disjoint n s
  disjoint B s
  disjoint K n
  disjoint .0. n
  disjoint B k
  disjoint B l
  disjoint k l
  disjoint M k
  disjoint M l
  disjoint N k
  disjoint N l
  disjoint R k
  disjoint R l
  disjoint T k
  disjoint T l
  disjoint Y k
  disjoint Y l
  disjoint b k
  disjoint b l
  disjoint k n
  disjoint k s
  disjoint l n
  disjoint l s
  disjoint .X. k
  disjoint .X. l
  disjoint .0. k
  disjoint .0. l
  disjoint .- k
  disjoint .- l
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) /\ K e. ( ZZ>= ` ( s + 2 ) ) ) -> ( ( K .^ X ) .x. ( G ` K ) ) = .0. )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vs
    cv
    #
    cn
    wcel
    #
    vb
    cv
    #
    cB
    cc0
    @4
    cfz
    co
    cmap
    co
    wcel
    #
    wa
    #
    cK
    @4
    c2
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    cK
    cX
    c.ex
    co
    #
    cK
    cG
    cfv
    #
    c.x
    co
    #
    c.0
    wceq
    #
    @3
    @8
    wa
    #
    @10
    cK
    cn0
    wcel
    #
    @4
    c1
    caddc
    co
    #
    cK
    clt
    wbr
    #
    wa
    #
    @14
    @8
    @10
    @19
    wi
    #
    @3
    @5
    @20
    @7
    @10
    @9
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @9
    cK
    cle
    wbr
    #
    w3a
    #
    @5
    @19
    @9
    cK
    eluz2
    @24
    @5
    @19
    @22
    @23
    @5
    @19
    wi
    @21
    @22
    @5
    @23
    @19
    @22
    @5
    wa
    #
    @23
    @19
    @25
    @23
    wa
    #
    @16
    @18
    @26
    @22
    cc0
    cK
    cle
    wbr
    #
    @16
    @22
    @5
    @23
    simpll
    @25
    @23
    @27
    @25
    cc0
    @9
    clt
    wbr
    #
    @23
    @27
    @5
    @22
    @28
    cc0
    @4
    clt
    wbr
    #
    @5
    @22
    @28
    wi
    @4
    nngt0
    @22
    @5
    @29
    @28
    @22
    @5
    @29
    @28
    wi
    @25
    @29
    @4
    @9
    clt
    wbr
    #
    @28
    @25
    @4
    c2
    @5
    @4
    cr
    wcel
    #
    @22
    @4
    nnre
    #
    adantl
    #
    c2
    crp
    wcel
    @25
    2rp
    a1i
    ltaddrpd
    @25
    cc0
    cr
    wcel
    #
    @31
    @9
    cr
    wcel
    #
    @29
    @30
    wa
    @28
    wi
    @25
    0red
    #
    @33
    @25
    @4
    c2
    @33
    c2
    cr
    wcel
    @25
    2re
    a1i
    readdcld
    #
    cc0
    @4
    @9
    lttr
    syl3anc
    mpan2d
    ex
    com13
    mpcom
    impcom
    @25
    @34
    @35
    cK
    cr
    wcel
    #
    @28
    @23
    wa
    @27
    wi
    @36
    @37
    @22
    @38
    @5
    cK
    zre
    adantr
    cc0
    @9
    cK
    ltleletr
    syl3anc
    mpand
    imp
    cK
    elnn0z
    sylanbrc
    @25
    @23
    @18
    @25
    @23
    @17
    c1
    caddc
    co
    #
    cK
    cle
    wbr
    #
    @18
    @25
    @9
    @39
    cK
    cle
    @25
    @39
    @9
    @5
    @39
    @9
    wceq
    #
    @22
    @5
    @4
    cc
    wcel
    @41
    @4
    nncn
    @4
    add1p1
    syl
    adantl
    eqcomd
    breq1d
    @25
    @17
    cz
    wcel
    #
    @22
    wa
    #
    @40
    @18
    wb
    @25
    @22
    @42
    @5
    @42
    @22
    @5
    @4
    @4
    nnz
    peano2zd
    anim2i
    ancomd
    @43
    @18
    @40
    @17
    cK
    zltp1le
    bicomd
    syl
    bitrd
    biimpa
    jca
    ex
    impancom
    3adant1
    com12
    syl5bi
    adantr
    adantl
    @15
    @16
    @18
    @14
    @15
    @16
    wa
    #
    @18
    wa
    #
    @13
    @11
    c.0
    c.x
    co
    #
    c.0
    @45
    @12
    c.0
    @11
    c.x
    @45
    vn
    cK
    vn
    cv
    #
    cc0
    wceq
    #
    c.0
    cM
    cT
    cfv
    #
    cc0
    @6
    cfv
    cT
    cfv
    c.xp
    co
    c.mi
    co
    #
    @47
    @17
    wceq
    #
    @4
    @6
    cfv
    cT
    cfv
    #
    @17
    @47
    clt
    wbr
    #
    c.0
    @47
    c1
    cmin
    co
    @6
    cfv
    cT
    cfv
    @49
    @47
    @6
    cfv
    cT
    cfv
    c.xp
    co
    c.mi
    co
    #
    cif
    #
    cif
    #
    cif
    #
    c.0
    cn0
    cG
    cvv
    cG
    vn
    cn0
    @57
    cmpt
    wceq
    @45
    chfacfisf.g
    a1i
    @45
    @47
    cK
    wceq
    #
    wa
    #
    @57
    @56
    @55
    c.0
    @59
    @48
    @50
    @56
    @59
    @48
    wn
    #
    cK
    cc0
    wceq
    #
    wn
    #
    @45
    @62
    @58
    @45
    cK
    cc0
    @45
    cK
    @45
    cc0
    @17
    cK
    @45
    0red
    @15
    @17
    cr
    wcel
    #
    @16
    @18
    @8
    @63
    @3
    @5
    @63
    @7
    @5
    @31
    @63
    @32
    @4
    peano2re
    syl
    adantr
    #
    adantl
    ad2antrr
    @16
    @38
    @15
    @18
    cK
    nn0re
    ad2antlr
    @44
    cc0
    @17
    clt
    wbr
    #
    @18
    @44
    @4
    cn0
    wcel
    #
    @65
    @8
    @66
    @3
    @16
    @5
    @66
    @7
    @4
    nnnn0
    adantr
    ad2antlr
    @4
    nn0p1gt0
    syl
    adantr
    @44
    @18
    simpr
    lttrd
    gt0ne0d
    neneqd
    adantr
    @58
    @60
    @62
    wb
    @45
    @58
    @48
    @61
    @47
    cK
    cc0
    eqeq1
    notbid
    adantl
    mpbird
    iffalsed
    @59
    @51
    @52
    @55
    @59
    @51
    wn
    #
    cK
    @17
    wceq
    #
    wn
    #
    @45
    @69
    @58
    @45
    cK
    @17
    @44
    @63
    @18
    cK
    @17
    wne
    @8
    @63
    @3
    @16
    @64
    ad2antlr
    @17
    cK
    ltne
    sylan
    neneqd
    adantr
    @58
    @67
    @69
    wb
    @45
    @58
    @51
    @68
    @47
    cK
    @17
    eqeq1
    notbid
    adantl
    mpbird
    iffalsed
    @59
    @53
    c.0
    @54
    @59
    @53
    @18
    @44
    @18
    @58
    simplr
    @58
    @53
    @18
    wb
    @45
    @47
    cK
    @17
    clt
    breq2
    adantl
    mpbird
    iftrued
    3eqtrd
    @15
    @16
    @18
    simplr
    c.0
    cvv
    wcel
    @45
    c.0
    cY
    c0g
    cfv
    cvv
    chfacfisf.0
    cY
    c0g
    fvex
    eqeltri
    a1i
    fvmptd
    oveq2d
    @45
    cY
    clmod
    wcel
    #
    @11
    cY
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @46
    c.0
    wceq
    @44
    @74
    @18
    @44
    @70
    @73
    @3
    @70
    @8
    @16
    @0
    @1
    @70
    @2
    @1
    @0
    cR
    crg
    wcel
    #
    @70
    cR
    crngring
    #
    cY
    cP
    cR
    cN
    chfacfisf.p
    chfacfisf.y
    pmatlmod
    sylan2
    3adant3
    ad2antrr
    @44
    @73
    @11
    cP
    cbs
    cfv
    #
    wcel
    #
    @44
    cP
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @16
    cX
    @77
    wcel
    #
    @78
    @3
    @80
    @8
    @16
    @3
    cP
    crg
    wcel
    #
    @80
    @1
    @0
    @82
    @2
    @1
    @75
    @82
    @76
    cP
    cR
    chfacfisf.p
    ply1ring
    syl
    3ad2ant2
    cP
    @79
    @79
    eqid
    #
    ringmgp
    syl
    ad2antrr
    @15
    @16
    simpr
    @3
    @81
    @8
    @16
    @3
    @75
    @81
    @1
    @0
    @75
    @2
    @76
    3ad2ant2
    @77
    cP
    cR
    cX
    chfacfscmulcl.x
    chfacfisf.p
    @77
    eqid
    #
    vr1cl
    syl
    ad2antrr
    @77
    c.ex
    @79
    cK
    cX
    @77
    cP
    @79
    @83
    @84
    mgpbas
    chfacfscmulcl.e
    mulgnn0cl
    syl3anc
    @3
    @73
    @78
    wb
    @8
    @16
    @3
    @72
    @77
    @11
    @3
    @71
    cP
    cbs
    @3
    cP
    @71
    @3
    @0
    cP
    ccrg
    wcel
    #
    wa
    #
    cP
    @71
    wceq
    @0
    @1
    @86
    @2
    @1
    @85
    @0
    cP
    cR
    chfacfisf.p
    ply1crng
    anim2i
    3adant3
    cY
    cP
    cN
    ccrg
    chfacfisf.y
    matsca2
    syl
    eqcomd
    fveq2d
    eleq2d
    ad2antrr
    mpbird
    jca
    adantr
    c.x
    @71
    @72
    cY
    @11
    c.0
    @71
    eqid
    chfacfscmulcl.m
    @72
    eqid
    chfacfisf.0
    lmodvs0
    syl
    eqtrd
    expl
    syld
    3impia
end
