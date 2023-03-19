include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cima.mm"
include "cc0.mm"
include "csn.mm"
include "wceq.mm"
include "cc.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wa.mm"
include "cun.mm"
include "cn0.mm"
include "cmap.mm"
include "wrex.mm"
include "wss.mm"
include "elply2.mm"
include "simprbi.mm"
include "simpll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprl.mm"
include "simprr.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "cbvsumv.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "syl5eq.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "coeidlem.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem coeid
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cN: class N
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let wph: wff ph
  let vm: setvar m
  let cB: class B
  let cM: class M
  let cX: class X
  assume dgrub.1: |- A = ( coeff ` F )
  assume dgrub.2: |- N = ( deg ` F )

  disjoint k z
  disjoint A k
  disjoint A z
  disjoint F k
  disjoint S k
  disjoint S z
  disjoint N k
  disjoint N z
  disjoint F z
  disjoint a k
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint F a
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint k ph
  disjoint ph z
  disjoint a m
  disjoint S a
  disjoint k m
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint S m
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint B k
  disjoint B z
  disjoint M k
  disjoint M y
  disjoint M z
  disjoint N a
  disjoint N n
  disjoint X k
  disjoint X z
  assert |- ( F e. ( Poly ` S ) -> F = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( ( A ` k ) x. ( z ^ k ) ) ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    va
    cv
    #
    vn
    cv
    #
    c1
    caddc
    co
    cuz
    cfv
    cima
    cc0
    csn
    #
    wceq
    #
    cF
    vx
    cc
    cc0
    @2
    cfz
    co
    #
    vm
    cv
    #
    @1
    cfv
    #
    vx
    cv
    #
    @6
    cexp
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cmpt
    #
    wceq
    #
    wa
    #
    va
    cS
    @3
    cun
    cn0
    cmap
    co
    #
    wrex
    vn
    cn0
    wrex
    #
    cF
    vz
    cc
    cc0
    cN
    cfz
    co
    vk
    cv
    #
    cA
    cfv
    vz
    cv
    #
    @17
    cexp
    co
    #
    cmul
    co
    vk
    csu
    cmpt
    wceq
    #
    @0
    cS
    cc
    wss
    @16
    vx
    cS
    vm
    vn
    cF
    va
    elply2
    simprbi
    @0
    @14
    @20
    vn
    va
    cn0
    @15
    @0
    @2
    cn0
    wcel
    #
    @1
    @15
    wcel
    #
    wa
    #
    wa
    #
    @14
    @20
    @24
    @14
    wa
    #
    vz
    cA
    @1
    cS
    vk
    cF
    @2
    cN
    dgrub.1
    dgrub.2
    @0
    @23
    @14
    simpll
    @0
    @21
    @22
    @14
    simplrl
    @0
    @21
    @22
    @14
    simplrr
    @24
    @4
    @13
    simprl
    @25
    cF
    @12
    vz
    cc
    @5
    @17
    @1
    cfv
    #
    @19
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    @24
    @4
    @13
    simprr
    vx
    vz
    cc
    @11
    @28
    @8
    @18
    wceq
    #
    @11
    @5
    @26
    @8
    @17
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    @28
    @5
    @10
    @31
    vm
    vk
    @6
    @17
    wceq
    @7
    @26
    @9
    @30
    cmul
    @6
    @17
    @1
    fveq2
    @6
    @17
    @8
    cexp
    oveq2
    oveq12d
    cbvsumv
    @29
    @5
    @31
    @27
    vk
    @29
    @30
    @19
    @26
    cmul
    @8
    @18
    @17
    cexp
    oveq1
    oveq2d
    sumeq2sdv
    syl5eq
    cbvmptv
    syl6eq
    coeidlem
    ex
    rexlimdvva
    mpd
end
