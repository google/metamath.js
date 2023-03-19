include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "ccoe.mm"
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
include "cn0.mm"
include "wrex.mm"
include "cmap.mm"
include "crab.mm"
include "crio.mm"
include "coeval.mm"
include "wreu.mm"
include "coeeu.mm"
include "riotacl2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "imaeq1.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylib.mm"

theorem coelem
  let vz: setvar z
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vj: setvar j
  let vm: setvar m
  let vw: setvar w
  let vx: setvar x
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cN: class N

  disjoint k z
  disjoint F n
  disjoint S n
  disjoint k n
  disjoint n z
  disjoint F k
  disjoint F z
  disjoint k y
  disjoint B k
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a f
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a w
  disjoint F a
  disjoint b f
  disjoint b j
  disjoint b m
  disjoint b n
  disjoint b w
  disjoint F b
  disjoint f j
  disjoint f m
  disjoint f n
  disjoint f w
  disjoint F f
  disjoint j m
  disjoint j n
  disjoint j w
  disjoint F j
  disjoint m n
  disjoint m w
  disjoint F m
  disjoint n w
  disjoint F w
  disjoint k x
  disjoint k ph
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S a
  disjoint S b
  disjoint S j
  disjoint S m
  disjoint S w
  disjoint a k
  disjoint a z
  disjoint b k
  disjoint b z
  disjoint f k
  disjoint f z
  disjoint j k
  disjoint j z
  disjoint k m
  disjoint k w
  disjoint m z
  disjoint w z
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint M k
  disjoint M z
  disjoint N k
  disjoint N z
  assert |- ( F e. ( Poly ` S ) -> ( ( coeff ` F ) e. ( CC ^m NN0 ) /\ E. n e. NN0 ( ( ( coeff ` F ) " ( ZZ>= ` ( n + 1 ) ) ) = { 0 } /\ F = ( z e. CC |-> sum_ k e. ( 0 ... n ) ( ( ( coeff ` F ) ` k ) x. ( z ^ k ) ) ) ) ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cF
    ccoe
    cfv
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
    #
    cima
    #
    cc0
    csn
    #
    wceq
    #
    cF
    vz
    cc
    cc0
    @3
    cfz
    co
    #
    vk
    cv
    #
    @2
    cfv
    #
    vz
    cv
    @9
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
    wceq
    #
    wa
    #
    vn
    cn0
    wrex
    #
    va
    cc
    cn0
    cmap
    co
    #
    crab
    #
    wcel
    @1
    @18
    wcel
    @1
    @4
    cima
    #
    @6
    wceq
    #
    cF
    vz
    cc
    @8
    @9
    @1
    cfv
    #
    @11
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
    wa
    #
    vn
    cn0
    wrex
    #
    wa
    @0
    @1
    @17
    va
    @18
    crio
    #
    @19
    vz
    cS
    vk
    vn
    cF
    va
    coeval
    @0
    @17
    va
    @18
    wreu
    @29
    @19
    wcel
    vz
    cS
    vk
    vn
    cF
    va
    coeeu
    @17
    va
    @18
    riotacl2
    syl
    eqeltrd
    @17
    @28
    va
    @1
    @18
    @2
    @1
    wceq
    #
    @16
    @27
    vn
    cn0
    @30
    @7
    @21
    @15
    @26
    @30
    @5
    @20
    @6
    @2
    @1
    @4
    imaeq1
    eqeq1d
    @30
    @14
    @25
    cF
    @30
    vz
    cc
    @13
    @24
    @30
    @8
    @12
    @23
    vk
    @30
    @10
    @22
    @11
    cmul
    @9
    @2
    @1
    fveq1
    oveq1d
    sumeq2sdv
    mpteq2dv
    eqeq2d
    anbi12d
    rexbidv
    elrab
    sylib
end
