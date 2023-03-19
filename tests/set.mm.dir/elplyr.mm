include "cc.mm"
include "wss.mm"
include "cn0.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "cmap.mm"
include "wrex.mm"
include "cply.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "ssun1.mm"
include "fss.mm"
include "sylancl.mm"
include "cvv.mm"
include "wb.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "cnex.mm"
include "ssexg.mm"
include "nn0ex.mm"
include "elmapg.mm"
include "mpbird.mm"
include "eqidd.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "elply.mm"
include "sylanbrc.mm"

theorem elplyr
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cN: class N
  let va: setvar a
  let vn: setvar n
  let vf: setvar f
  let vx: setvar x
  let cT: class T
  let cF: class F

  disjoint k z
  disjoint A k
  disjoint A z
  disjoint N k
  disjoint N z
  disjoint S k
  disjoint S z
  disjoint a k
  disjoint a n
  disjoint a z
  disjoint A a
  disjoint k n
  disjoint n z
  disjoint A n
  disjoint N a
  disjoint N n
  disjoint a f
  disjoint a x
  disjoint S a
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f z
  disjoint S f
  disjoint k x
  disjoint n x
  disjoint S n
  disjoint x z
  disjoint S x
  disjoint T a
  disjoint T f
  disjoint T k
  disjoint T n
  disjoint T z
  disjoint F a
  disjoint F f
  disjoint F n
  disjoint F k
  disjoint F z
  assert |- ( ( S C_ CC /\ N e. NN0 /\ A : NN0 --> S ) -> ( z e. CC |-> sum_ k e. ( 0 ... N ) ( ( A ` k ) x. ( z ^ k ) ) ) e. ( Poly ` S ) )

  proof
    cS
    cc
    wss
    #
    cN
    cn0
    wcel
    #
    cn0
    cS
    cA
    wf
    #
    w3a
    #
    @0
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    vz
    cv
    @5
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    vz
    cc
    cc0
    vn
    cv
    #
    cfz
    co
    #
    @5
    va
    cv
    #
    cfv
    #
    @7
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    wceq
    #
    va
    cS
    cc0
    csn
    #
    cun
    #
    cn0
    cmap
    co
    #
    wrex
    vn
    cn0
    wrex
    #
    @10
    cS
    cply
    cfv
    wcel
    @0
    @1
    @2
    simp1
    #
    @3
    @1
    cA
    @21
    wcel
    #
    @10
    @10
    wceq
    #
    @22
    @0
    @1
    @2
    simp2
    @3
    @24
    cn0
    @20
    cA
    wf
    #
    @3
    @2
    cS
    @20
    wss
    @26
    @0
    @1
    @2
    simp3
    cS
    @19
    ssun1
    cn0
    cS
    @20
    cA
    fss
    sylancl
    @3
    @20
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    @24
    @26
    wb
    @3
    @20
    cc
    wss
    cc
    cvv
    wcel
    @27
    @3
    cS
    @19
    cc
    @23
    @3
    cc0
    cc
    @3
    0cnd
    snssd
    unssd
    cnex
    @20
    cc
    cvv
    ssexg
    sylancl
    nn0ex
    @20
    cn0
    cA
    cvv
    cvv
    elmapg
    sylancl
    mpbird
    @3
    @10
    eqidd
    @18
    @25
    @10
    vz
    cc
    @4
    @15
    vk
    csu
    #
    cmpt
    #
    wceq
    vn
    va
    cN
    cA
    cn0
    @21
    @11
    cN
    wceq
    #
    @17
    @29
    @10
    @30
    vz
    cc
    @16
    @28
    @30
    @12
    @4
    @15
    vk
    @11
    cN
    cc0
    cfz
    oveq2
    sumeq1d
    mpteq2dv
    eqeq2d
    @13
    cA
    wceq
    #
    @29
    @10
    @10
    @31
    vz
    cc
    @28
    @9
    @31
    @4
    @15
    @8
    vk
    @31
    @14
    @6
    @7
    cmul
    @5
    @13
    cA
    fveq1
    oveq1d
    sumeq2sdv
    mpteq2dv
    eqeq2d
    rspc2ev
    syl3anc
    vz
    cS
    vk
    vn
    @10
    va
    elply
    sylanbrc
end
