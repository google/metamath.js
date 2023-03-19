include "wcel.mm"
include "wa.mm"
include "csubma.mm"
include "co.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmpt2.mm"
include "cminmar1.mm"
include "wceq.mm"
include "eqid.mm"
include "submaval.mm"
include "3anidm23.mm"
include "fveq2d.mm"
include "cur.mm"
include "c0g.mm"
include "cif.mm"
include "csymg.mm"
include "cbs.mm"
include "czrh.mm"
include "cpsgn.mm"
include "ccom.mm"
include "cmgp.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "minmar1val.mm"
include "ccrg.mm"
include "marep01ma.mm"
include "mdetleib2.mm"
include "sylancr.mm"
include "adantr.mm"
include "crab.mm"
include "cplusg.mm"
include "ccmn.mm"
include "crg.mm"
include "crngring.mm"
include "ringcmn.mm"
include "mp2b.mm"
include "a1i.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "symgbasfi.mm"
include "syl.mm"
include "smadiadetlem1.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "cun.mm"
include "wss.mm"
include "ssrab2.mm"
include "undif.mm"
include "sylib.mm"
include "eqcomd.mm"
include "gsummptfidmsplit.mm"
include "smadiadetlem4.mm"
include "smadiadetlem2.mm"
include "oveq12d.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "diffi.mm"
include "cmat.mm"
include "simpll.mm"
include "difssd.mm"
include "submabas.mm"
include "syl2anc.mm"
include "simpr.mm"
include "madetsmelbas2.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "mndrid.mm"
include "jctil.mm"
include "sylan2.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem smadiadet
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cE: class E
  let cK: class K
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  assume smadiadet.a: |- A = ( N Mat R )
  assume smadiadet.b: |- B = ( Base ` A )
  assume smadiadet.r: |- R e. CRing
  assume smadiadet.d: |- D = ( N maDet R )
  assume smadiadet.h: |- E = ( ( N \ { K } ) maDet R )


  assert |- ( ( M e. B /\ K e. N ) -> ( E ` ( K ( ( N subMat R ) ` M ) K ) ) = ( D ` ( K ( ( N minMatR1 R ) ` M ) K ) ) )

  proof
    cM
    cB
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    #
    cK
    cK
    cM
    cN
    cR
    csubma
    co
    #
    cfv
    co
    #
    cE
    cfv
    vi
    vj
    cN
    cK
    csn
    #
    cdif
    #
    @6
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cmpt2
    #
    cE
    cfv
    #
    cK
    cK
    cM
    cN
    cR
    cminmar1
    co
    #
    cfv
    co
    #
    cD
    cfv
    #
    @2
    @4
    @10
    cE
    @0
    @1
    @4
    @10
    wceq
    cA
    cB
    @3
    cR
    vi
    vj
    cK
    cK
    cM
    cN
    smadiadet.a
    @3
    eqid
    smadiadet.b
    submaval
    3anidm23
    fveq2d
    @2
    @14
    vi
    vj
    cN
    cN
    @7
    cK
    wceq
    @8
    cK
    wceq
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    @9
    cif
    cmpt2
    #
    cD
    cfv
    #
    cR
    vp
    cN
    csymg
    cfv
    #
    cbs
    cfv
    #
    vp
    cv
    #
    cR
    czrh
    cfv
    #
    cN
    cpsgn
    cfv
    #
    ccom
    cfv
    cR
    cmgp
    cfv
    #
    vn
    cN
    vn
    cv
    #
    @25
    @21
    cfv
    #
    @17
    co
    cmpt
    cgsu
    co
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    cgsu
    co
    #
    @11
    @2
    @13
    @17
    cD
    @0
    @1
    @13
    @17
    wceq
    cA
    cB
    @12
    cR
    @15
    vi
    vj
    cK
    cK
    cM
    cN
    @16
    smadiadet.a
    smadiadet.b
    @12
    eqid
    @15
    eqid
    #
    @16
    eqid
    #
    minmar1val
    3anidm23
    fveq2d
    @0
    @18
    @29
    wceq
    #
    @1
    @0
    cR
    ccrg
    wcel
    #
    @17
    cB
    wcel
    @32
    smadiadet.r
    cA
    cB
    cR
    @15
    vi
    cK
    cK
    cM
    cN
    @16
    vj
    smadiadet.a
    smadiadet.b
    smadiadet.r
    @31
    @30
    marep01ma
    vn
    cA
    cB
    cD
    @20
    cR
    @23
    @27
    @24
    @17
    cN
    @22
    vp
    smadiadet.d
    smadiadet.a
    smadiadet.b
    @20
    eqid
    #
    @22
    eqid
    #
    @23
    eqid
    #
    @27
    eqid
    #
    @24
    eqid
    #
    mdetleib2
    sylancr
    adantr
    @2
    @29
    cR
    vp
    cK
    vq
    cv
    cfv
    cK
    wceq
    #
    vq
    @20
    crab
    #
    @28
    cmpt
    cgsu
    co
    #
    cR
    vp
    @20
    @40
    cdif
    #
    @28
    cmpt
    cgsu
    co
    #
    cR
    cplusg
    cfv
    #
    co
    cR
    vp
    @6
    csymg
    cfv
    #
    cbs
    cfv
    #
    @21
    @22
    @6
    cpsgn
    cfv
    #
    ccom
    cfv
    @24
    vn
    @6
    @25
    @26
    @10
    co
    cmpt
    cgsu
    co
    @27
    co
    #
    cmpt
    cgsu
    co
    #
    @16
    @44
    co
    #
    @11
    @2
    @20
    cR
    cbs
    cfv
    #
    @40
    @42
    @44
    vp
    cR
    @28
    @51
    eqid
    #
    @44
    eqid
    #
    cR
    ccmn
    wcel
    #
    @2
    @33
    cR
    crg
    wcel
    #
    @54
    smadiadet.r
    cR
    crngring
    #
    cR
    ringcmn
    mp2b
    a1i
    #
    @0
    @20
    cfn
    wcel
    #
    @1
    @0
    cN
    cfn
    wcel
    #
    @58
    @0
    @59
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    smadiadet.a
    smadiadet.b
    matrcl
    simpld
    #
    cN
    @20
    @19
    @19
    eqid
    @34
    symgbasfi
    syl
    adantr
    cA
    cB
    @20
    cR
    @23
    @27
    @15
    vi
    vj
    vn
    @24
    cK
    cM
    cN
    @22
    @16
    vp
    smadiadet.a
    smadiadet.b
    smadiadet.r
    @31
    @30
    @34
    @38
    @35
    @36
    @37
    smadiadetlem1
    @40
    @42
    cin
    c0
    wceq
    @2
    @40
    @20
    disjdif
    a1i
    @2
    @40
    @42
    cun
    #
    @20
    @2
    @40
    @20
    wss
    #
    @61
    @20
    wceq
    @62
    @2
    @39
    vq
    @20
    ssrab2
    a1i
    @40
    @20
    undif
    sylib
    eqcomd
    gsummptfidmsplit
    @2
    @41
    @49
    @43
    @16
    @44
    cA
    cB
    @20
    cR
    @23
    @27
    @15
    vi
    vj
    vn
    @24
    cK
    cM
    cN
    @46
    @22
    @16
    @47
    vq
    vp
    smadiadet.a
    smadiadet.b
    smadiadet.r
    @31
    @30
    @34
    @38
    @35
    @36
    @37
    @46
    eqid
    #
    @47
    eqid
    #
    smadiadetlem4
    cA
    cB
    @20
    cR
    @23
    @27
    @15
    vi
    vj
    vn
    @24
    cK
    cM
    cN
    @22
    @16
    vq
    vp
    smadiadet.a
    smadiadet.b
    smadiadet.r
    @31
    @30
    @34
    @38
    @35
    @36
    @37
    smadiadetlem2
    oveq12d
    @2
    @50
    @49
    @11
    @2
    cR
    cmnd
    wcel
    #
    @49
    @51
    wcel
    @50
    @49
    wceq
    @33
    @55
    @65
    smadiadet.r
    @56
    cR
    ringmnd
    mp2b
    @2
    @51
    vp
    cR
    @46
    @48
    @52
    @57
    @2
    @6
    cfn
    wcel
    #
    @46
    cfn
    wcel
    @0
    @66
    @1
    @0
    @59
    @66
    @60
    cN
    @5
    diffi
    syl
    adantr
    @6
    @46
    @45
    @45
    eqid
    @63
    symgbasfi
    syl
    @2
    @48
    @51
    wcel
    #
    vp
    @46
    @2
    @21
    @46
    wcel
    #
    wa
    #
    @33
    @10
    @6
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    @68
    @67
    @33
    @69
    smadiadet.r
    a1i
    @69
    @0
    @6
    cN
    wss
    #
    @72
    @0
    @1
    @68
    simpll
    @69
    cN
    @5
    difssd
    cA
    cB
    @6
    cR
    vi
    vj
    cM
    cN
    smadiadet.a
    smadiadet.b
    submabas
    #
    syl2anc
    @2
    @68
    simpr
    @70
    @71
    @46
    @21
    cR
    @47
    vn
    @24
    @10
    @6
    @22
    @63
    @64
    @35
    @70
    eqid
    #
    @71
    eqid
    #
    @38
    madetsmelbas2
    syl3anc
    ralrimiva
    gsummptcl
    @51
    @44
    cR
    @49
    @16
    @52
    @53
    @31
    mndrid
    sylancr
    @2
    @33
    @72
    wa
    #
    @11
    @49
    wceq
    @1
    @0
    @73
    @77
    @1
    cN
    @5
    difssd
    @0
    @73
    wa
    @72
    @33
    @74
    smadiadet.r
    jctil
    sylan2
    vn
    @70
    @71
    cE
    @46
    cR
    @47
    @27
    @24
    @10
    @6
    @22
    vp
    smadiadet.h
    @75
    @76
    @63
    @35
    @64
    @37
    @38
    mdetleib2
    syl
    eqtr4d
    3eqtrd
    3eqtrd
    eqtr4d
end
