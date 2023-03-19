include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cmpt2.mm"
include "cpl1.mm"
include "cascl.mm"
include "cpm2mval.mm"
include "fveq2d.mm"
include "cmat.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "eqid.mm"
include "cn0.mm"
include "simp3.mm"
include "cpmatpmat.mm"
include "3ad2ant1.mm"
include "matecld.mm"
include "0nn0.mm"
include "coe1fvalcl.mm"
include "sylancl.mm"
include "matbas2d.mm"
include "mat2pmatval.mm"
include "syl3anc.mm"
include "cvv.mm"
include "eqidd.mm"
include "wa.mm"
include "oveq12.mm"
include "fveq1d.mm"
include "adantl.mm"
include "fvexd.mm"
include "ovmpt2d.mm"
include "mpt2eq3dva.mm"
include "eqtrd.mm"
include "wral.mm"
include "m2cpminvid2lem.mm"
include "wb.mm"
include "simpl2.mm"
include "simprl.mm"
include "simprr.mm"
include "adantr.mm"
include "ply1sclcl.mm"
include "syl2anc.mm"
include "ply1coe1eq.mm"
include "bicomd.mm"
include "mpbird.mm"
include "ralrimivva.mm"
include "simplr.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "anasss.mm"
include "2ralbidva.mm"
include "eqmat.mm"
include "3eqtrd.mm"

theorem m2cpminvid2
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  assume m2cpminvid2.s: |- S = ( N ConstPolyMat R )
  assume m2cpminvid2.i: |- I = ( N cPolyMatToMat R )
  assume m2cpminvid2.t: |- T = ( N matToPolyMat R )


  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. S ) -> ( T ` ( I ` M ) ) = M )

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
    cM
    cI
    cfv
    #
    cT
    cfv
    vx
    vy
    cN
    cN
    cc0
    vx
    cv
    #
    vy
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
    cmpt2
    #
    cT
    cfv
    #
    vi
    vj
    cN
    cN
    cc0
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
    cpl1
    cfv
    #
    cascl
    cfv
    #
    cfv
    #
    cmpt2
    #
    cM
    @3
    @4
    @10
    cT
    vx
    vy
    cR
    cS
    cI
    cM
    cN
    crg
    m2cpminvid2.i
    m2cpminvid2.s
    cpm2mval
    fveq2d
    @3
    @11
    vi
    vj
    cN
    cN
    @12
    @13
    @10
    co
    #
    @18
    cfv
    #
    cmpt2
    #
    @20
    @3
    @0
    @1
    @10
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    @11
    @23
    wceq
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    @3
    vx
    vy
    @24
    @25
    @9
    cR
    cR
    cbs
    cfv
    #
    cN
    crg
    @24
    eqid
    #
    @28
    eqid
    #
    @25
    eqid
    #
    @26
    @27
    @3
    @5
    cN
    wcel
    #
    @6
    cN
    wcel
    #
    w3a
    #
    @7
    @17
    cbs
    cfv
    #
    wcel
    #
    cc0
    cn0
    wcel
    #
    @9
    @28
    wcel
    #
    @34
    cN
    @17
    cmat
    co
    #
    @39
    cbs
    cfv
    #
    @17
    @5
    @6
    @35
    cM
    cN
    @39
    eqid
    #
    @35
    eqid
    #
    @40
    eqid
    #
    @3
    @32
    @33
    simp2
    @3
    @32
    @33
    simp3
    @3
    @32
    cM
    @40
    wcel
    #
    @33
    @40
    @39
    @17
    cR
    cS
    cM
    cN
    crg
    m2cpminvid2.s
    @17
    eqid
    #
    @41
    @43
    cpmatpmat
    #
    3ad2ant1
    matecld
    0nn0
    @8
    @35
    @17
    cR
    @7
    @28
    cc0
    @8
    eqid
    #
    @42
    @45
    @30
    coe1fvalcl
    #
    sylancl
    matbas2d
    vi
    vj
    @24
    @25
    @17
    cR
    @18
    cT
    @10
    cN
    crg
    m2cpminvid2.t
    @29
    @31
    @45
    @18
    eqid
    #
    mat2pmatval
    syl3anc
    @3
    vi
    vj
    cN
    cN
    @22
    @19
    @3
    @12
    cN
    wcel
    #
    @13
    cN
    wcel
    #
    w3a
    #
    @21
    @16
    @18
    @52
    vx
    vy
    @12
    @13
    cN
    cN
    @9
    @16
    @10
    cvv
    @52
    @10
    eqidd
    @5
    @12
    wceq
    @6
    @13
    wceq
    wa
    #
    @9
    @16
    wceq
    @52
    @53
    cc0
    @8
    @15
    @53
    @7
    @14
    cco1
    @5
    @12
    @6
    @13
    cM
    oveq12
    fveq2d
    fveq1d
    adantl
    @3
    @50
    @51
    simp2
    #
    @3
    @50
    @51
    simp3
    #
    @52
    cc0
    @15
    fvexd
    ovmpt2d
    fveq2d
    mpt2eq3dva
    eqtrd
    @3
    @20
    cM
    wceq
    #
    @5
    @6
    @20
    co
    #
    @7
    wceq
    #
    vy
    cN
    wral
    vx
    cN
    wral
    #
    @3
    @59
    @9
    @18
    cfv
    #
    @7
    wceq
    #
    vy
    cN
    wral
    vx
    cN
    wral
    @3
    @61
    vx
    vy
    cN
    cN
    @3
    @32
    @33
    wa
    #
    wa
    #
    @61
    vn
    cv
    #
    @60
    cco1
    cfv
    #
    cfv
    @64
    @8
    cfv
    wceq
    vn
    cn0
    wral
    #
    vx
    vy
    @17
    cR
    cS
    vn
    cM
    cN
    m2cpminvid2.s
    @45
    m2cpminvid2lem
    @63
    @1
    @60
    @35
    wcel
    #
    @36
    @61
    @66
    wb
    @0
    @1
    @2
    @62
    simpl2
    #
    @63
    @1
    @38
    @67
    @68
    @63
    @36
    @37
    @38
    @63
    @39
    @40
    @17
    @5
    @6
    @35
    cM
    cN
    @41
    @42
    @43
    @3
    @32
    @33
    simprl
    @3
    @32
    @33
    simprr
    @3
    @44
    @62
    @46
    adantr
    matecld
    #
    0nn0
    @48
    sylancl
    @18
    @35
    @17
    cR
    @9
    @28
    @45
    @49
    @30
    @42
    ply1sclcl
    syl2anc
    @69
    @1
    @67
    @36
    w3a
    @66
    @61
    @65
    @35
    @8
    @17
    cR
    vn
    @60
    @7
    @45
    @42
    @65
    eqid
    @47
    ply1coe1eq
    bicomd
    syl3anc
    mpbird
    ralrimivva
    @3
    @58
    @61
    vx
    vy
    cN
    cN
    @3
    @32
    @33
    @58
    @61
    wb
    @3
    @32
    wa
    #
    @33
    wa
    #
    @57
    @60
    @7
    @71
    vi
    vj
    @5
    @6
    cN
    cN
    @19
    @60
    @20
    cvv
    @71
    @20
    eqidd
    @12
    @5
    wceq
    @13
    @6
    wceq
    wa
    #
    @19
    @60
    wceq
    @71
    @72
    @16
    @9
    @18
    @72
    cc0
    @15
    @8
    @72
    @14
    @7
    cco1
    @12
    @5
    @13
    @6
    cM
    oveq12
    fveq2d
    fveq1d
    fveq2d
    adantl
    @3
    @32
    @33
    simplr
    @70
    @33
    simpr
    @71
    @9
    @18
    fvexd
    ovmpt2d
    eqeq1d
    anasss
    2ralbidva
    mpbird
    @3
    @20
    @40
    wcel
    @44
    @56
    @59
    wb
    @3
    vi
    vj
    @39
    @40
    @19
    @17
    @35
    cN
    cvv
    @41
    @42
    @43
    @26
    @3
    cR
    cpl1
    fvexd
    @52
    @1
    @16
    @28
    wcel
    #
    @19
    @35
    wcel
    @3
    @50
    @1
    @51
    @27
    3ad2ant1
    @52
    @14
    @35
    wcel
    @37
    @73
    @52
    @39
    @40
    @17
    @12
    @13
    @35
    cM
    cN
    @41
    @42
    @43
    @54
    @55
    @3
    @50
    @44
    @51
    @46
    3ad2ant1
    matecld
    0nn0
    @15
    @35
    @17
    cR
    @14
    @28
    cc0
    @15
    eqid
    @42
    @45
    @30
    coe1fvalcl
    sylancl
    @18
    @35
    @17
    cR
    @16
    @28
    @45
    @49
    @30
    @42
    ply1sclcl
    syl2anc
    matbas2d
    @46
    @39
    @40
    @17
    vx
    vy
    cN
    @20
    cM
    @41
    @43
    eqmat
    syl2anc
    mpbird
    3eqtrd
end
