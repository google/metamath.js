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
include "crg.mm"
include "cbs.mm"
include "crngring.mm"
include "pmatring.mm"
include "sylan2.mm"
include "3adant3.mm"
include "cmgp.mm"
include "cmnd.mm"
include "eqid.mm"
include "ringmgp.mm"
include "mat2pmatbas.mm"
include "syl3an2.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "expl.mm"
include "syld.mm"
include "3impia.mm"

theorem chfacfpmmul0
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let c.xp: class .X.
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  let vb: setvar b
  assume cayhamlem1.a: |- A = ( N Mat R )
  assume cayhamlem1.b: |- B = ( Base ` A )
  assume cayhamlem1.p: |- P = ( Poly1 ` R )
  assume cayhamlem1.y: |- Y = ( N Mat P )
  assume cayhamlem1.r: |- .X. = ( .r ` Y )
  assume cayhamlem1.s: |- .- = ( -g ` Y )
  assume cayhamlem1.0: |- .0. = ( 0g ` Y )
  assume cayhamlem1.t: |- T = ( N matToPolyMat R )
  assume cayhamlem1.g: |- G = ( n e. NN0 |-> if ( n = 0 , ( .0. .- ( ( T ` M ) .X. ( T ` ( b ` 0 ) ) ) ) , if ( n = ( s + 1 ) , ( T ` ( b ` s ) ) , if ( ( s + 1 ) < n , .0. , ( ( T ` ( b ` ( n - 1 ) ) ) .- ( ( T ` M ) .X. ( T ` ( b ` n ) ) ) ) ) ) ) )
  assume cayhamlem1.e: |- .^ = ( .g ` ( mulGrp ` Y ) )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint Y n
  disjoint b n
  disjoint n s
  disjoint K n
  disjoint .0. n
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN /\ b e. ( B ^m ( 0 ... s ) ) ) /\ K e. ( ZZ>= ` ( s + 2 ) ) ) -> ( ( K .^ ( T ` M ) ) .X. ( G ` K ) ) = .0. )

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
    cM
    cT
    cfv
    #
    c.ex
    co
    #
    cK
    cG
    cfv
    #
    c.xp
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
    @15
    @8
    @10
    @20
    wi
    #
    @3
    @5
    @21
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
    @20
    @9
    cK
    eluz2
    @25
    @5
    @20
    @23
    @24
    @5
    @20
    wi
    @22
    @23
    @5
    @24
    @20
    @23
    @5
    wa
    #
    @24
    @20
    @26
    @24
    wa
    #
    @17
    @19
    @27
    @23
    cc0
    cK
    cle
    wbr
    #
    @17
    @23
    @5
    @24
    simpll
    @26
    @24
    @28
    @26
    cc0
    @9
    clt
    wbr
    #
    @24
    @28
    @5
    @23
    @29
    cc0
    @4
    clt
    wbr
    #
    @5
    @23
    @29
    wi
    @4
    nngt0
    @23
    @5
    @30
    @29
    @23
    @5
    @30
    @29
    wi
    @26
    @30
    @4
    @9
    clt
    wbr
    #
    @29
    @26
    @4
    c2
    @5
    @4
    cr
    wcel
    #
    @23
    @4
    nnre
    #
    adantl
    #
    c2
    crp
    wcel
    @26
    2rp
    a1i
    ltaddrpd
    @26
    cc0
    cr
    wcel
    #
    @32
    @9
    cr
    wcel
    #
    @30
    @31
    wa
    @29
    wi
    @26
    0red
    #
    @34
    @26
    @4
    c2
    @34
    c2
    cr
    wcel
    @26
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
    @26
    @35
    @36
    cK
    cr
    wcel
    #
    @29
    @24
    wa
    @28
    wi
    @37
    @38
    @23
    @39
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
    @26
    @24
    @19
    @26
    @24
    @18
    c1
    caddc
    co
    #
    cK
    cle
    wbr
    #
    @19
    @26
    @9
    @40
    cK
    cle
    @26
    @40
    @9
    @5
    @40
    @9
    wceq
    #
    @23
    @5
    @4
    cc
    wcel
    @42
    @4
    nncn
    @4
    add1p1
    syl
    adantl
    eqcomd
    breq1d
    @26
    @18
    cz
    wcel
    #
    @23
    wa
    #
    @41
    @19
    wb
    @26
    @23
    @43
    @5
    @43
    @23
    @5
    @4
    @4
    nnz
    peano2zd
    anim2i
    ancomd
    @44
    @19
    @41
    @18
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
    @16
    @17
    @19
    @15
    @16
    @17
    wa
    #
    @19
    wa
    #
    @14
    @12
    c.0
    c.xp
    co
    #
    c.0
    @46
    @13
    c.0
    @12
    c.xp
    @46
    vn
    cK
    vn
    cv
    #
    cc0
    wceq
    #
    c.0
    @11
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
    @48
    @18
    wceq
    #
    @4
    @6
    cfv
    cT
    cfv
    #
    @18
    @48
    clt
    wbr
    #
    c.0
    @48
    c1
    cmin
    co
    @6
    cfv
    cT
    cfv
    @11
    @48
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
    @46
    cayhamlem1.g
    a1i
    @46
    @48
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
    @49
    @50
    @56
    @59
    @49
    wn
    #
    cK
    cc0
    wceq
    #
    wn
    #
    @46
    @62
    @58
    @46
    cK
    cc0
    @46
    cK
    @46
    cc0
    @18
    cK
    @46
    0red
    @16
    @18
    cr
    wcel
    #
    @17
    @19
    @8
    @63
    @3
    @5
    @63
    @7
    @5
    @32
    @63
    @33
    @4
    peano2re
    syl
    adantr
    #
    adantl
    ad2antrr
    @17
    @39
    @16
    @19
    cK
    nn0re
    ad2antlr
    @45
    cc0
    @18
    clt
    wbr
    #
    @19
    @45
    @4
    cn0
    wcel
    #
    @65
    @8
    @66
    @3
    @17
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
    @45
    @19
    simpr
    lttrd
    gt0ne0d
    neneqd
    adantr
    @58
    @60
    @62
    wb
    @46
    @58
    @49
    @61
    @48
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
    @18
    wceq
    #
    wn
    #
    @46
    @69
    @58
    @46
    cK
    @18
    @45
    @63
    @19
    cK
    @18
    wne
    @8
    @63
    @3
    @17
    @64
    ad2antlr
    @18
    cK
    ltne
    sylan
    neneqd
    adantr
    @58
    @67
    @69
    wb
    @46
    @58
    @51
    @68
    @48
    cK
    @18
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
    @19
    @45
    @19
    @58
    simplr
    @58
    @53
    @19
    wb
    @46
    @48
    cK
    @18
    clt
    breq2
    adantl
    mpbird
    iftrued
    3eqtrd
    @16
    @17
    @19
    simplr
    c.0
    cvv
    wcel
    @46
    c.0
    cY
    c0g
    cfv
    cvv
    cayhamlem1.0
    cY
    c0g
    fvex
    eqeltri
    a1i
    fvmptd
    oveq2d
    @46
    cY
    crg
    wcel
    #
    @12
    cY
    cbs
    cfv
    #
    wcel
    #
    @47
    c.0
    wceq
    @16
    @70
    @17
    @19
    @3
    @70
    @8
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
    cayhamlem1.p
    cayhamlem1.y
    pmatring
    sylan2
    3adant3
    #
    adantr
    ad2antrr
    @45
    @72
    @19
    @45
    cY
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @17
    @11
    @71
    wcel
    #
    @72
    @3
    @77
    @8
    @17
    @3
    @70
    @77
    @75
    cY
    @76
    @76
    eqid
    #
    ringmgp
    syl
    ad2antrr
    @16
    @17
    simpr
    @3
    @78
    @8
    @17
    @1
    @0
    @73
    @2
    @78
    @74
    cA
    cB
    cY
    cP
    cR
    cT
    cM
    cN
    cayhamlem1.t
    cayhamlem1.a
    cayhamlem1.b
    cayhamlem1.p
    cayhamlem1.y
    mat2pmatbas
    syl3an2
    ad2antrr
    @71
    c.ex
    @76
    cK
    @11
    @71
    cY
    @76
    @79
    @71
    eqid
    #
    mgpbas
    cayhamlem1.e
    mulgnn0cl
    syl3anc
    adantr
    @71
    cY
    c.xp
    @12
    c.0
    @80
    cayhamlem1.r
    cayhamlem1.0
    ringrz
    syl2anc
    eqtrd
    expl
    syld
    3impia
end
