include "cfusgr.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "c2.mm"
include "cwwspthsn.mm"
include "co.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "crab.mm"
include "cmpt.mm"
include "ciun.mm"
include "csu.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "mpteq2i.mm"
include "fusgreg2wsp.mm"
include "ad2antrr.mm"
include "fveq2d.mm"
include "fusgrvtxfi.mm"
include "cfn.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "eqid.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cvtx.mm"
include "wspthnfi.mm"
include "rabfi.mm"
include "3syl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wdisj.mm"
include "2wspmdisj.mm"
include "a1i.mm"
include "hashiun.mm"
include "wi.mm"
include "fusgreghash2wspv.mm"
include "ralim.mm"
include "syl.mm"
include "imp.mm"
include "fveq2.mm"
include "rspccva.mm"
include "sylan.mm"
include "sumeq2dv.mm"
include "cc.mm"
include "cn0.mm"
include "fusgrregdegfi.mm"
include "nn0cnd.mm"
include "kcnktkm1cn.mm"
include "fsumconst.mm"
include "syl2an2r.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "ex.mm"

theorem fusgreghash2wsp
  let vv: setvar v
  let cG: class G
  let cK: class K
  let cV: class V
  let va: setvar a
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  assume fusgreghash2wsp.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint K v
  disjoint V v
  disjoint G a
  disjoint G s
  disjoint G t
  disjoint G y
  disjoint a s
  disjoint a t
  disjoint a v
  disjoint a y
  disjoint s t
  disjoint s v
  disjoint s y
  disjoint t v
  disjoint t y
  disjoint v y
  disjoint K y
  disjoint V a
  disjoint V s
  disjoint V t
  disjoint V y
  assert |- ( ( G e. FinUSGraph /\ V =/= (/) ) -> ( A. v e. V ( ( VtxDeg ` G ) ` v ) = K -> ( # ` ( 2 WSPathsN G ) ) = ( ( # ` V ) x. ( K x. ( K - 1 ) ) ) ) )

  proof
    cG
    cfusgr
    wcel
    #
    cV
    c0
    wne
    #
    wa
    #
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    #
    cfv
    cK
    wceq
    #
    vv
    cV
    wral
    #
    c2
    cG
    cwwspthsn
    co
    #
    chash
    cfv
    #
    cV
    chash
    cfv
    cK
    cK
    c1
    cmin
    co
    cmul
    co
    #
    cmul
    co
    #
    wceq
    @2
    @6
    wa
    #
    @8
    vy
    cV
    vy
    cv
    #
    va
    cV
    c1
    vs
    cv
    #
    cfv
    #
    va
    cv
    #
    wceq
    #
    vs
    @7
    crab
    #
    cmpt
    #
    cfv
    #
    ciun
    #
    chash
    cfv
    #
    cV
    @19
    chash
    cfv
    #
    vy
    csu
    #
    @10
    @11
    @7
    @20
    chash
    @0
    @7
    @20
    wceq
    @1
    @6
    vy
    vt
    cG
    @18
    cV
    va
    fusgreghash2wsp.v
    va
    cV
    @17
    c1
    vt
    cv
    #
    cfv
    #
    @15
    wceq
    #
    vt
    @7
    crab
    @16
    @26
    vs
    vt
    @7
    @13
    @24
    wceq
    @14
    @25
    @15
    c1
    @13
    @24
    fveq1
    eqeq1d
    cbvrabv
    mpteq2i
    #
    fusgreg2wsp
    ad2antrr
    fveq2d
    @0
    @21
    @23
    wceq
    @1
    @6
    @0
    vy
    cV
    @19
    cG
    cV
    fusgreghash2wsp.v
    fusgrvtxfi
    #
    @0
    @12
    cV
    wcel
    #
    wa
    @19
    @14
    @12
    wceq
    #
    vs
    @7
    crab
    #
    cfn
    @29
    @19
    @31
    wceq
    @0
    va
    @12
    @17
    @31
    cV
    @18
    @15
    @12
    wceq
    @16
    @30
    vs
    @7
    @15
    @12
    @14
    eqeq2
    rabbidv
    @18
    eqid
    @30
    vs
    @7
    c2
    cG
    cwwspthsn
    ovex
    rabex
    fvmpt
    adantl
    @0
    @31
    cfn
    wcel
    #
    @29
    @0
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    @7
    cfn
    wcel
    @32
    cG
    @33
    @33
    eqid
    fusgrvtxfi
    cG
    c2
    wspthnfi
    @30
    vs
    @7
    rabfi
    3syl
    adantr
    eqeltrd
    vy
    cV
    @19
    wdisj
    @0
    vy
    vt
    cG
    @18
    cV
    va
    fusgreghash2wsp.v
    @27
    2wspmdisj
    a1i
    hashiun
    ad2antrr
    @11
    @23
    cV
    @9
    vy
    csu
    #
    @10
    @11
    cV
    @22
    @9
    vy
    @11
    @3
    @18
    cfv
    #
    chash
    cfv
    #
    @9
    wceq
    #
    vv
    cV
    wral
    #
    @29
    @22
    @9
    wceq
    #
    @2
    @6
    @38
    @0
    @6
    @38
    wi
    #
    @1
    @0
    @5
    @37
    wi
    vv
    cV
    wral
    @40
    vt
    vv
    cG
    cK
    @18
    cV
    va
    fusgreghash2wsp.v
    @27
    fusgreghash2wspv
    @5
    @37
    vv
    cV
    ralim
    syl
    adantr
    imp
    @37
    @39
    vv
    @12
    cV
    @3
    @12
    wceq
    #
    @36
    @22
    @9
    @41
    @35
    @19
    chash
    @3
    @12
    @18
    fveq2
    fveq2d
    eqeq1d
    rspccva
    sylan
    sumeq2dv
    @2
    cV
    cfn
    wcel
    #
    @6
    @9
    cc
    wcel
    #
    @34
    @10
    wceq
    @0
    @42
    @1
    @28
    adantr
    @11
    cK
    cc
    wcel
    @43
    @11
    cK
    @2
    @6
    cK
    cn0
    wcel
    vv
    @4
    cG
    cK
    cV
    fusgreghash2wsp.v
    @4
    eqid
    fusgrregdegfi
    imp
    nn0cnd
    cK
    kcnktkm1cn
    syl
    cV
    @9
    vy
    fsumconst
    syl2an2r
    eqtrd
    3eqtrd
    ex
end
