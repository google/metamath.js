include "wcel.mm"
include "cn.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
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
include "nnex.mm"
include "ovex.mm"
include "iunex.mm"
include "fvmptd.mm"
include "c1.mm"
include "relexp1g.mm"
include "sseq1d.mm"
include "anbi1d.mm"
include "wral.mm"
include "caddc.mm"
include "oveq2.mm"
include "imbi2d.mm"
include "weq.mm"
include "simprl.mm"
include "w3a.mm"
include "simp1.mm"
include "1nn.mm"
include "simp2l.mm"
include "relexpaddnn.mm"
include "syl3anc.mm"
include "simp2rr.mm"
include "simp3.mm"
include "simp2rl.mm"
include "trrelssd.mm"
include "eqsstr3d.mm"
include "3exp.mm"
include "a2d.mm"
include "nnind.mm"
include "com12.mm"
include "ralrimiv.mm"
include "iunss.mm"
include "sylibr.mm"
include "ex.mm"
include "sylbird.mm"
include "sseq1.mm"
include "syl5ibr.mm"
include "mpcom.mm"
include "alrimiv.mm"

theorem iunrelexpmin1
  let cC: class C
  let cR: class R
  let vn: setvar n
  let cN: class N
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume iunrelexpmin1.def: |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) )

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
  assert |- ( ( R e. V /\ N = NN ) -> A. s ( ( R C_ s /\ ( s o. s ) C_ s ) -> ( C ` R ) C_ s ) )

  proof
    cR
    cV
    wcel
    #
    cN
    cn
    wceq
    #
    wa
    #
    cR
    vs
    cv
    #
    wss
    #
    @3
    @3
    ccom
    @3
    wss
    #
    wa
    #
    cR
    cC
    cfv
    #
    @3
    wss
    #
    wi
    #
    vs
    @7
    vn
    cn
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
    @9
    @2
    vr
    cR
    vn
    cN
    vr
    cv
    #
    @10
    crelexp
    co
    #
    ciun
    #
    @12
    cvv
    cC
    cvv
    cC
    vr
    cvv
    @16
    cmpt
    wceq
    @2
    iunrelexpmin1.def
    a1i
    @2
    @14
    cR
    wceq
    #
    wa
    #
    vn
    cN
    cn
    @15
    @11
    @0
    @1
    @17
    simplr
    @18
    @14
    cR
    @10
    crelexp
    @2
    @17
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
    @12
    cvv
    wcel
    @2
    vn
    cn
    @11
    nnex
    cR
    @10
    crelexp
    ovex
    iunex
    a1i
    fvmptd
    @2
    @9
    @13
    @6
    @12
    @3
    wss
    #
    wi
    #
    @0
    @20
    @1
    @0
    @6
    cR
    c1
    crelexp
    co
    #
    @3
    wss
    #
    @5
    wa
    #
    @19
    @0
    @22
    @4
    @5
    @0
    @21
    cR
    @3
    cR
    cV
    relexp1g
    sseq1d
    anbi1d
    @0
    @23
    @19
    @0
    @23
    wa
    #
    @11
    @3
    wss
    #
    vn
    cn
    wral
    @19
    @24
    @25
    vn
    cn
    @10
    cn
    wcel
    @24
    @25
    @24
    cR
    vx
    cv
    #
    crelexp
    co
    #
    @3
    wss
    #
    wi
    @24
    @22
    wi
    @24
    cR
    vy
    cv
    #
    crelexp
    co
    #
    @3
    wss
    #
    wi
    @24
    cR
    @29
    c1
    caddc
    co
    #
    crelexp
    co
    #
    @3
    wss
    #
    wi
    @24
    @25
    wi
    vx
    vy
    @10
    @26
    c1
    wceq
    #
    @28
    @22
    @24
    @35
    @27
    @21
    @3
    @26
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
    @28
    @31
    @24
    @36
    @27
    @30
    @3
    @26
    @29
    cR
    crelexp
    oveq2
    sseq1d
    imbi2d
    @26
    @32
    wceq
    #
    @28
    @34
    @24
    @37
    @27
    @33
    @3
    @26
    @32
    cR
    crelexp
    oveq2
    sseq1d
    imbi2d
    vx
    vn
    weq
    #
    @28
    @25
    @24
    @38
    @27
    @11
    @3
    @26
    @10
    cR
    crelexp
    oveq2
    sseq1d
    imbi2d
    @0
    @22
    @5
    simprl
    @29
    cn
    wcel
    #
    @24
    @31
    @34
    @39
    @24
    @31
    @34
    @39
    @24
    @31
    w3a
    #
    @33
    @30
    @21
    ccom
    #
    @3
    @40
    @39
    c1
    cn
    wcel
    #
    @0
    @41
    @33
    wceq
    @39
    @24
    @31
    simp1
    @42
    @40
    1nn
    a1i
    @39
    @0
    @23
    @31
    simp2l
    cR
    c1
    @29
    cV
    relexpaddnn
    syl3anc
    @40
    @3
    @30
    @21
    @22
    @5
    @0
    @39
    @31
    simp2rr
    @39
    @24
    @31
    simp3
    @22
    @5
    @0
    @39
    @31
    simp2rl
    trrelssd
    eqsstr3d
    3exp
    a2d
    nnind
    com12
    ralrimiv
    vn
    cn
    @11
    @3
    iunss
    sylibr
    ex
    sylbird
    adantr
    @13
    @8
    @19
    @6
    @7
    @12
    @3
    sseq1
    imbi2d
    syl5ibr
    mpcom
    alrimiv
end
