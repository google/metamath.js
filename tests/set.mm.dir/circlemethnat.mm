include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "co.mm"
include "cexp.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "cneg.mm"
include "cv.mm"
include "ce.mm"
include "cfv.mm"
include "citg.mm"
include "wceq.mm"
include "wtru.mm"
include "cn.mm"
include "crepr.mm"
include "cfzo.mm"
include "cind.mm"
include "csn.mm"
include "cxp.mm"
include "cprod.mm"
include "csu.mm"
include "cvts.mm"
include "chash.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "cpr.mm"
include "wss.mm"
include "cvv.mm"
include "nnex.mm"
include "indf.mm"
include "mp2an.mm"
include "cr.mm"
include "pr01ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "fss.mm"
include "cnex.mm"
include "elmap.mm"
include "mpbir.mm"
include "elexi.mm"
include "fvconst2.mm"
include "adantl.mm"
include "fveq1d.mm"
include "prodeq2dv.mm"
include "sumeq2dv.mm"
include "a1i.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "hashrepr.mm"
include "eqtr4d.mm"
include "syl6reqr.mm"
include "fconst6.mm"
include "circlemeth.mm"
include "cfn.mm"
include "fzofi.mm"
include "ioossre.mm"
include "sselda.mm"
include "vtscl.mm"
include "syl5eqel.mm"
include "fprodconst.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "adantr.mm"
include "hashfzo0.mm"
include "syl.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "itgeq2dv.mm"
include "3eqtrd.mm"
include "trud.mm"

theorem circlemethnat
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cN: class N
  let va: setvar a
  let vc: setvar c
  assume circlemethnat.r: |- R = ( # ` ( A ( repr ` S ) N ) )
  assume circlemethnat.f: |- F = ( ( ( ( _Ind ` NN ) ` A ) vts N ) ` x )
  assume circlemethnat.n: |- N e. NN0
  assume circlemethnat.a: |- A C_ NN
  assume circlemethnat.s: |- S e. NN

  disjoint A x
  disjoint N x
  disjoint S x
  disjoint A a
  disjoint A c
  disjoint a c
  disjoint a x
  disjoint c x
  disjoint F a
  disjoint N a
  disjoint N c
  disjoint S a
  disjoint S c
  assert |- R = S. ( 0 (,) 1 ) ( ( F ^ S ) x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x

  proof
    cR
    vx
    cc0
    c1
    cioo
    co
    #
    cF
    cS
    cexp
    co
    #
    ci
    c2
    cpi
    cmul
    co
    cmul
    co
    cN
    cneg
    vx
    cv
    #
    cmul
    co
    cmul
    co
    ce
    cfv
    #
    cmul
    co
    #
    citg
    #
    wceq
    wtru
    cR
    cn
    cN
    cS
    crepr
    cfv
    #
    co
    #
    cc0
    cS
    cfzo
    co
    #
    va
    cv
    #
    vc
    cv
    #
    cfv
    #
    @9
    @8
    cA
    cn
    cind
    cfv
    cfv
    #
    csn
    cxp
    #
    cfv
    #
    cfv
    #
    va
    cprod
    #
    vc
    csu
    #
    vx
    @0
    @8
    @2
    @14
    cN
    cvts
    co
    #
    cfv
    #
    va
    cprod
    #
    @3
    cmul
    co
    #
    citg
    @5
    wtru
    @17
    cA
    cN
    @6
    co
    chash
    cfv
    #
    cR
    wtru
    @17
    @7
    @8
    @11
    @12
    cfv
    #
    va
    cprod
    #
    vc
    csu
    @22
    wtru
    @7
    @16
    @24
    vc
    wtru
    @10
    @7
    wcel
    wa
    #
    @8
    @15
    @23
    va
    @25
    @9
    @8
    wcel
    #
    wa
    @11
    @14
    @12
    @26
    @14
    @12
    wceq
    #
    @25
    @8
    @12
    @9
    @12
    cc
    cn
    cmap
    co
    #
    @12
    @28
    wcel
    cn
    cc
    @12
    wf
    #
    cn
    cc0
    c1
    cpr
    #
    @12
    wf
    #
    @30
    cc
    wss
    @29
    cn
    cvv
    wcel
    cA
    cn
    wss
    #
    @31
    nnex
    circlemethnat.a
    cA
    cn
    cvv
    indf
    mp2an
    @30
    cr
    cc
    pr01ssre
    ax-resscn
    sstri
    cn
    @30
    cc
    @12
    fss
    mp2an
    #
    cc
    cn
    @12
    cnex
    nnex
    elmap
    mpbir
    #
    elexi
    fvconst2
    #
    adantl
    fveq1d
    prodeq2dv
    sumeq2dv
    wtru
    cA
    cS
    cN
    va
    vc
    @32
    wtru
    circlemethnat.a
    a1i
    cN
    cn0
    wcel
    #
    wtru
    circlemethnat.n
    a1i
    #
    wtru
    cS
    cS
    cn
    wcel
    wtru
    circlemethnat.s
    a1i
    #
    nnnn0d
    #
    hashrepr
    eqtr4d
    circlemethnat.r
    syl6reqr
    wtru
    vx
    cS
    @13
    cN
    va
    vc
    @37
    @38
    @8
    @28
    @13
    wf
    wtru
    @8
    @12
    @28
    @34
    fconst6
    a1i
    circlemeth
    wtru
    vx
    @0
    @21
    @4
    wtru
    @2
    @0
    wcel
    #
    wa
    #
    @20
    @1
    @3
    cmul
    @41
    @8
    cF
    va
    cprod
    #
    cF
    @8
    chash
    cfv
    #
    cexp
    co
    #
    @20
    @1
    @41
    @8
    cfn
    wcel
    #
    cF
    cc
    wcel
    @42
    @44
    wceq
    @45
    @41
    cc0
    cS
    fzofi
    a1i
    @41
    cF
    @2
    @12
    cN
    cvts
    co
    #
    cfv
    #
    cc
    circlemethnat.f
    @41
    @12
    cN
    @2
    @36
    @41
    circlemethnat.n
    a1i
    wtru
    @0
    cc
    @2
    @0
    cc
    wss
    wtru
    @0
    cr
    cc
    cc0
    c1
    ioossre
    ax-resscn
    sstri
    a1i
    sselda
    @29
    @41
    @33
    a1i
    vtscl
    syl5eqel
    @8
    cF
    va
    fprodconst
    syl2anc
    @41
    @8
    cF
    @19
    va
    @41
    @26
    wa
    #
    @19
    @47
    cF
    @48
    @2
    @18
    @46
    @48
    @14
    @12
    cN
    cvts
    @26
    @27
    @41
    @35
    adantl
    oveq1d
    fveq1d
    circlemethnat.f
    syl6reqr
    prodeq2dv
    @41
    @43
    cS
    cF
    cexp
    @41
    cS
    cn0
    wcel
    #
    @43
    cS
    wceq
    wtru
    @49
    @40
    @39
    adantr
    cS
    hashfzo0
    syl
    oveq2d
    3eqtr3d
    oveq1d
    itgeq2dv
    3eqtrd
    trud
end
