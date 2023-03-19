include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
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
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wa.mm"
include "cn0.mm"
include "wrex.mm"
include "cmap.mm"
include "crio.mm"
include "plyssc.mm"
include "sseli.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "riotabidv.mm"
include "df-coe.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem coeval
  let vz: setvar z
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let va: setvar a
  let vy: setvar y
  let cB: class B
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
  disjoint a n
  disjoint F a
  disjoint F n
  disjoint S a
  disjoint S n
  disjoint a k
  disjoint a z
  disjoint k n
  disjoint n z
  disjoint k y
  disjoint B k
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a f
  disjoint a j
  disjoint a m
  disjoint a w
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
  disjoint S b
  disjoint S j
  disjoint S m
  disjoint S w
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
  assert |- ( F e. ( Poly ` S ) -> ( coeff ` F ) = ( iota_ a e. ( CC ^m NN0 ) E. n e. NN0 ( ( a " ( ZZ>= ` ( n + 1 ) ) ) = { 0 } /\ F = ( z e. CC |-> sum_ k e. ( 0 ... n ) ( ( a ` k ) x. ( z ^ k ) ) ) ) ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    cF
    cc
    cply
    cfv
    #
    wcel
    cF
    ccoe
    cfv
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
    wceq
    #
    cF
    vz
    cc
    cc0
    @3
    cfz
    co
    vk
    cv
    #
    @2
    cfv
    vz
    cv
    @5
    cexp
    co
    cmul
    co
    vk
    csu
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
    crio
    #
    wceq
    @0
    @1
    cF
    cS
    plyssc
    sseli
    vf
    cF
    @4
    vf
    cv
    #
    @6
    wceq
    #
    wa
    #
    vn
    cn0
    wrex
    #
    va
    @10
    crio
    @11
    @1
    ccoe
    @12
    cF
    wceq
    #
    @15
    @9
    va
    @10
    @16
    @14
    @8
    vn
    cn0
    @16
    @13
    @7
    @4
    @12
    cF
    @6
    eqeq1
    anbi2d
    rexbidv
    riotabidv
    vz
    vf
    vk
    vn
    va
    df-coe
    @9
    va
    @10
    riotaex
    fvmpt
    syl
end
