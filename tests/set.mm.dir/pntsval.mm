include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "clog.mm"
include "cdiv.mm"
include "cchp.mm"
include "caddc.mm"
include "cmul.mm"
include "csu.mm"
include "cr.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvsumv.mm"
include "oveq2d.mm"
include "wcel.mm"
include "oveq1.mm"
include "adantr.mm"
include "sumeq12dv.mm"
include "syl5eq.mm"
include "sumex.mm"
include "fvmpt.mm"

theorem pntsval
  let cA: class A
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let va: setvar a
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let wph: wff ph
  let cR: class R
  let cT: class T
  assume pntsval.1: |- S = ( a e. RR |-> sum_ i e. ( 1 ... ( |_ ` a ) ) ( ( Lam ` i ) x. ( ( log ` i ) + ( psi ` ( a / i ) ) ) ) )

  disjoint a i
  disjoint a n
  disjoint A a
  disjoint i n
  disjoint A i
  disjoint A n
  disjoint S n
  disjoint a c
  disjoint a k
  disjoint a m
  disjoint a x
  disjoint a y
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint i k
  disjoint i m
  disjoint i x
  disjoint i y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint S c
  disjoint S k
  disjoint S m
  disjoint S x
  disjoint S y
  disjoint R c
  disjoint R m
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint T m
  disjoint T n
  assert |- ( A e. RR -> ( S ` A ) = sum_ n e. ( 1 ... ( |_ ` A ) ) ( ( Lam ` n ) x. ( ( log ` n ) + ( psi ` ( A / n ) ) ) ) )

  proof
    va
    cA
    c1
    va
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vi
    cv
    #
    cvma
    cfv
    #
    @3
    clog
    cfv
    #
    @0
    @3
    cdiv
    co
    #
    cchp
    cfv
    #
    caddc
    co
    #
    cmul
    co
    #
    vi
    csu
    #
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cvma
    cfv
    #
    @13
    clog
    cfv
    #
    cA
    @13
    cdiv
    co
    #
    cchp
    cfv
    #
    caddc
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    cr
    cS
    @0
    cA
    wceq
    #
    @10
    @2
    @14
    @15
    @0
    @13
    cdiv
    co
    #
    cchp
    cfv
    #
    caddc
    co
    #
    cmul
    co
    #
    vn
    csu
    @20
    @2
    @9
    @25
    vi
    vn
    @3
    @13
    wceq
    #
    @4
    @14
    @8
    @24
    cmul
    @3
    @13
    cvma
    fveq2
    @26
    @5
    @15
    @7
    @23
    caddc
    @3
    @13
    clog
    fveq2
    @26
    @6
    @22
    cchp
    @3
    @13
    @0
    cdiv
    oveq2
    fveq2d
    oveq12d
    oveq12d
    cbvsumv
    @21
    @2
    @12
    @25
    @19
    vn
    @21
    @1
    @11
    c1
    cfz
    @0
    cA
    cfl
    fveq2
    oveq2d
    @21
    @25
    @19
    wceq
    @13
    @2
    wcel
    @21
    @24
    @18
    @14
    cmul
    @21
    @23
    @17
    @15
    caddc
    @21
    @22
    @16
    cchp
    @0
    cA
    @13
    cdiv
    oveq1
    fveq2d
    oveq2d
    oveq2d
    adantr
    sumeq12dv
    syl5eq
    pntsval.1
    @12
    @19
    vn
    sumex
    fvmpt
end
