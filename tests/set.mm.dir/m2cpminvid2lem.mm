include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "cc0.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cascl.mm"
include "wceq.mm"
include "cn.mm"
include "csn.mm"
include "cun.mm"
include "wral.mm"
include "cn0.mm"
include "c0g.mm"
include "cmat.mm"
include "cbs.mm"
include "eqid.mm"
include "cpmatelimp.mm"
include "3impia.mm"
include "simpr.mm"
include "syl.mm"
include "adantr.mm"
include "wi.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "adantl.mm"
include "fveq2.mm"
include "cbvralv.mm"
include "cif.mm"
include "cmpt.mm"
include "simpl2.mm"
include "simprl.mm"
include "cpmatpmat.mm"
include "matecld.mm"
include "0nn0.mm"
include "coe1fvalcl.mm"
include "sylancl.mm"
include "jca.mm"
include "coe1scl.mm"
include "cvv.mm"
include "eqidd.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "nnnn0.mm"
include "fvex.mm"
include "ifex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "wn.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "3eqtrd.mm"
include "eqcom.mm"
include "biimpi.mm"
include "sylan9eq.mm"
include "ex.mm"
include "ralimdva.mm"
include "imp.mm"
include "ply1sclid.mm"
include "eqcomd.mm"
include "syl5bi.mm"
include "syld.mm"
include "mpd.mm"
include "wb.mm"
include "c0ex.mm"
include "eqeq12d.mm"
include "ralunsn.mm"
include "mp1i.mm"
include "mpbird.mm"
include "df-n0.mm"
include "raleqi.mm"
include "sylibr.mm"

theorem m2cpminvid2lem
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  assume m2cpminvid2lem.s: |- S = ( N ConstPolyMat R )
  assume m2cpminvid2lem.p: |- P = ( Poly1 ` R )

  disjoint M n
  disjoint N n
  disjoint P n
  disjoint R n
  disjoint S n
  disjoint n x
  disjoint n y
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint M l
  disjoint l n
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint P l
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R l
  disjoint S l
  disjoint i x
  disjoint j x
  disjoint k x
  disjoint j y
  disjoint k y
  disjoint k n
  disjoint l x
  disjoint l y
  assert |- ( ( ( N e. Fin /\ R e. Ring /\ M e. S ) /\ ( x e. N /\ y e. N ) ) -> A. n e. NN0 ( ( coe1 ` ( ( algSc ` P ) ` ( ( coe1 ` ( x M y ) ) ` 0 ) ) ) ` n ) = ( ( coe1 ` ( x M y ) ) ` n ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cS
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cN
    wcel
    #
    vy
    cv
    #
    cN
    wcel
    #
    wa
    #
    wa
    #
    vn
    cv
    #
    cc0
    @4
    @6
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cP
    cascl
    cfv
    #
    cfv
    cco1
    cfv
    #
    cfv
    #
    @10
    @12
    cfv
    #
    wceq
    #
    vn
    cn
    cc0
    csn
    cun
    #
    wral
    #
    @18
    vn
    cn0
    wral
    @9
    @20
    @18
    vn
    cn
    wral
    #
    cc0
    @15
    cfv
    #
    @13
    wceq
    #
    wa
    #
    @9
    vk
    cv
    #
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    vk
    cn
    wral
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @24
    @3
    @34
    @8
    @3
    cM
    cN
    cP
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    @34
    wa
    #
    @34
    @0
    @1
    @2
    @38
    @36
    @35
    cP
    cR
    cS
    vi
    vj
    vk
    cM
    cN
    m2cpminvid2lem.s
    m2cpminvid2lem.p
    @35
    eqid
    #
    @36
    eqid
    #
    cpmatelimp
    3impia
    @37
    @34
    simpr
    syl
    adantr
    @9
    @34
    @25
    @12
    cfv
    #
    @31
    wceq
    #
    vk
    cn
    wral
    #
    @24
    @8
    @34
    @43
    wi
    @3
    @33
    @43
    @25
    @4
    @27
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @31
    wceq
    #
    vk
    cn
    wral
    vi
    vj
    @4
    @6
    cN
    cN
    @26
    @4
    wceq
    #
    @32
    @47
    vk
    cn
    @48
    @30
    @46
    @31
    @48
    @25
    @29
    @45
    @48
    @28
    @44
    cco1
    @26
    @4
    @27
    cM
    oveq1
    fveq2d
    fveq1d
    eqeq1d
    ralbidv
    @27
    @6
    wceq
    #
    @47
    @42
    vk
    cn
    @49
    @46
    @41
    @31
    @49
    @25
    @45
    @12
    @49
    @44
    @11
    cco1
    @27
    @6
    @4
    cM
    oveq2
    fveq2d
    fveq1d
    eqeq1d
    ralbidv
    rspc2v
    adantl
    @43
    @17
    @31
    wceq
    #
    vn
    cn
    wral
    #
    @9
    @24
    @42
    @50
    vk
    vn
    cn
    @25
    @10
    wceq
    @41
    @17
    @31
    @25
    @10
    @12
    fveq2
    eqeq1d
    cbvralv
    @9
    @51
    @24
    @9
    @51
    wa
    #
    @21
    @23
    @9
    @51
    @21
    @9
    @50
    @18
    vn
    cn
    @9
    @10
    cn
    wcel
    #
    wa
    #
    @50
    @18
    @54
    @50
    @16
    @31
    @17
    @54
    @16
    @10
    vl
    cn0
    vl
    cv
    #
    cc0
    wceq
    #
    @13
    @31
    cif
    #
    cmpt
    #
    cfv
    @10
    cc0
    wceq
    #
    @13
    @31
    cif
    #
    @31
    @54
    @10
    @15
    @58
    @54
    @1
    @13
    cR
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @15
    @58
    wceq
    @9
    @63
    @53
    @9
    @1
    @62
    @0
    @1
    @2
    @8
    simpl2
    @9
    @11
    cP
    cbs
    cfv
    #
    wcel
    cc0
    cn0
    wcel
    @62
    @9
    @35
    @36
    cP
    @4
    @6
    @64
    cM
    cN
    @39
    @64
    eqid
    #
    @40
    @3
    @5
    @7
    simprl
    @8
    @7
    @3
    @5
    @7
    simpr
    adantl
    @3
    @37
    @8
    @36
    @35
    cP
    cR
    cS
    cM
    cN
    crg
    m2cpminvid2lem.s
    m2cpminvid2lem.p
    @39
    @40
    cpmatpmat
    adantr
    matecld
    0nn0
    @12
    @64
    cP
    cR
    @11
    @61
    cc0
    @12
    eqid
    @65
    m2cpminvid2lem.p
    @61
    eqid
    #
    coe1fvalcl
    sylancl
    jca
    #
    adantr
    vl
    @14
    cP
    cR
    @61
    @13
    @31
    m2cpminvid2lem.p
    @14
    eqid
    #
    @66
    @31
    eqid
    coe1scl
    syl
    fveq1d
    @54
    vl
    @10
    @57
    @60
    cn0
    @58
    cvv
    @54
    @58
    eqidd
    @55
    @10
    wceq
    #
    @57
    @60
    wceq
    @54
    @69
    @56
    @59
    @13
    @31
    @55
    @10
    cc0
    eqeq1
    ifbid
    adantl
    @53
    @10
    cn0
    wcel
    @9
    @10
    nnnn0
    adantl
    @60
    cvv
    wcel
    @54
    @59
    @13
    @31
    cc0
    @12
    fvex
    cR
    c0g
    fvex
    ifex
    a1i
    fvmptd
    @54
    @59
    @13
    @31
    @53
    @59
    wn
    @9
    @53
    @10
    cc0
    @10
    nnne0
    neneqd
    adantl
    iffalsed
    3eqtrd
    @50
    @31
    @17
    wceq
    @17
    @31
    eqcom
    biimpi
    sylan9eq
    ex
    ralimdva
    imp
    @52
    @63
    @23
    @9
    @63
    @51
    @67
    adantr
    @63
    @13
    @22
    @14
    cP
    cR
    @61
    @13
    m2cpminvid2lem.p
    @68
    @66
    ply1sclid
    eqcomd
    syl
    jca
    ex
    syl5bi
    syld
    mpd
    cc0
    cvv
    wcel
    @20
    @24
    wb
    @9
    c0ex
    @18
    @23
    vn
    cn
    cc0
    cvv
    @59
    @16
    @22
    @17
    @13
    @10
    cc0
    @15
    fveq2
    @10
    cc0
    @12
    fveq2
    eqeq12d
    ralunsn
    mp1i
    mpbird
    @18
    vn
    cn0
    @19
    df-n0
    raleqi
    sylibr
end
