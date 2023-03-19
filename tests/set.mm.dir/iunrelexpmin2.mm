include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "wa.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "w3a.mm"
include "cfv.mm"
include "wi.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "simplr.mm"
include "simpr.mm"
include "oveq1d.mm"
include "iuneq12d.mm"
include "elex.mm"
include "adantr.mm"
include "nn0ex.mm"
include "ovex.mm"
include "iunex.mm"
include "fvmptd.mm"
include "cc0.mm"
include "c1.mm"
include "relexp0g.mm"
include "sseq1d.mm"
include "relexp1g.mm"
include "3anbi12d.mm"
include "wral.mm"
include "cn.mm"
include "wo.mm"
include "elnn0.mm"
include "caddc.mm"
include "oveq2.mm"
include "imbi2d.mm"
include "weq.mm"
include "simpr2.mm"
include "simp1.mm"
include "1nn.mm"
include "simp2l.mm"
include "relexpaddnn.mm"
include "syl3anc.mm"
include "simp2r3.mm"
include "simp3.mm"
include "simp2r2.mm"
include "trrelssd.mm"
include "eqsstr3d.mm"
include "3exp.mm"
include "a2d.mm"
include "nnind.mm"
include "simpr1.mm"
include "syl5ibr.mm"
include "jaoi.mm"
include "sylbi.mm"
include "com12.mm"
include "ralrimiv.mm"
include "iunss.mm"
include "sylibr.mm"
include "ex.mm"
include "sylbird.mm"
include "sseq1.mm"
include "mpcom.mm"
include "alrimiv.mm"

theorem iunrelexpmin2
  let cC: class C
  let cR: class R
  let vn: setvar n
  let cN: class N
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume iunrelexpmin2.def: |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) )

  disjoint N s
  disjoint n r
  disjoint R n
  disjoint R r
  disjoint R s
  disjoint V n
  disjoint V r
  disjoint V s
  disjoint n s
  disjoint n r
  disjoint C n
  disjoint N n
  disjoint C r
  disjoint N r
  disjoint C N
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint V x
  disjoint V y
  disjoint n x
  assert |- ( ( R e. V /\ N = NN0 ) -> A. s ( ( ( _I |` ( dom R u. ran R ) ) C_ s /\ R C_ s /\ ( s o. s ) C_ s ) -> ( C ` R ) C_ s ) )

  proof
    cR
    cV
    wcel
    #
    cN
    cn0
    wceq
    #
    wa
    #
    cid
    cR
    cdm
    cR
    crn
    cun
    cres
    #
    vs
    cv
    #
    wss
    #
    cR
    @4
    wss
    #
    @4
    @4
    ccom
    @4
    wss
    #
    w3a
    #
    cR
    cC
    cfv
    #
    @4
    wss
    #
    wi
    #
    vs
    @9
    vn
    cn0
    cR
    vn
    cv
    #
    crelexp
    co
    #
    ciun
    #
    wceq
    #
    @2
    @11
    @2
    vr
    cR
    vn
    cN
    vr
    cv
    #
    @12
    crelexp
    co
    #
    ciun
    #
    @14
    cvv
    cC
    cvv
    cC
    vr
    cvv
    @18
    cmpt
    wceq
    @2
    iunrelexpmin2.def
    a1i
    @2
    @16
    cR
    wceq
    #
    wa
    #
    vn
    cN
    cn0
    @17
    @13
    @0
    @1
    @19
    simplr
    @20
    @16
    cR
    @12
    crelexp
    @2
    @19
    simpr
    oveq1d
    iuneq12d
    @0
    cR
    cvv
    wcel
    @1
    cR
    cV
    elex
    adantr
    @14
    cvv
    wcel
    @2
    vn
    cn0
    @13
    nn0ex
    cR
    @12
    crelexp
    ovex
    iunex
    a1i
    fvmptd
    @2
    @11
    @15
    @8
    @14
    @4
    wss
    #
    wi
    #
    @0
    @22
    @1
    @0
    @8
    cR
    cc0
    crelexp
    co
    #
    @4
    wss
    #
    cR
    c1
    crelexp
    co
    #
    @4
    wss
    #
    @7
    w3a
    #
    @21
    @0
    @24
    @5
    @26
    @6
    @7
    @0
    @23
    @3
    @4
    cR
    cV
    relexp0g
    sseq1d
    @0
    @25
    cR
    @4
    cR
    cV
    relexp1g
    sseq1d
    3anbi12d
    @0
    @27
    @21
    @0
    @27
    wa
    #
    @13
    @4
    wss
    #
    vn
    cn0
    wral
    @21
    @28
    @29
    vn
    cn0
    @12
    cn0
    wcel
    #
    @28
    @29
    @30
    @12
    cn
    wcel
    #
    @12
    cc0
    wceq
    #
    wo
    @28
    @29
    wi
    #
    @12
    elnn0
    @31
    @33
    @32
    @28
    cR
    vx
    cv
    #
    crelexp
    co
    #
    @4
    wss
    #
    wi
    @28
    @26
    wi
    @28
    cR
    vy
    cv
    #
    crelexp
    co
    #
    @4
    wss
    #
    wi
    @28
    cR
    @37
    c1
    caddc
    co
    #
    crelexp
    co
    #
    @4
    wss
    #
    wi
    @33
    vx
    vy
    @12
    @34
    c1
    wceq
    #
    @36
    @26
    @28
    @43
    @35
    @25
    @4
    @34
    c1
    cR
    crelexp
    oveq2
    sseq1d
    imbi2d
    vx
    vy
    weq
    #
    @36
    @39
    @28
    @44
    @35
    @38
    @4
    @34
    @37
    cR
    crelexp
    oveq2
    sseq1d
    imbi2d
    @34
    @40
    wceq
    #
    @36
    @42
    @28
    @45
    @35
    @41
    @4
    @34
    @40
    cR
    crelexp
    oveq2
    sseq1d
    imbi2d
    vx
    vn
    weq
    #
    @36
    @29
    @28
    @46
    @35
    @13
    @4
    @34
    @12
    cR
    crelexp
    oveq2
    sseq1d
    imbi2d
    @0
    @24
    @26
    @7
    simpr2
    @37
    cn
    wcel
    #
    @28
    @39
    @42
    @47
    @28
    @39
    @42
    @47
    @28
    @39
    w3a
    #
    @41
    @38
    @25
    ccom
    #
    @4
    @48
    @47
    c1
    cn
    wcel
    #
    @0
    @49
    @41
    wceq
    @47
    @28
    @39
    simp1
    @50
    @48
    1nn
    a1i
    @47
    @0
    @27
    @39
    simp2l
    cR
    c1
    @37
    cV
    relexpaddnn
    syl3anc
    @48
    @4
    @38
    @25
    @24
    @26
    @7
    @0
    @47
    @39
    simp2r3
    @47
    @28
    @39
    simp3
    @24
    @26
    @7
    @0
    @47
    @39
    simp2r2
    trrelssd
    eqsstr3d
    3exp
    a2d
    nnind
    @28
    @29
    @32
    @24
    @0
    @24
    @26
    @7
    simpr1
    @32
    @13
    @23
    @4
    @12
    cc0
    cR
    crelexp
    oveq2
    sseq1d
    syl5ibr
    jaoi
    sylbi
    com12
    ralrimiv
    vn
    cn0
    @13
    @4
    iunss
    sylibr
    ex
    sylbird
    adantr
    @15
    @10
    @21
    @8
    @9
    @14
    @4
    sseq1
    imbi2d
    syl5ibr
    mpcom
    alrimiv
end
