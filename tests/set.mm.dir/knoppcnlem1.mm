include "cv.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cfv.mm"
include "cn0.mm"
include "cvv.mm"
include "cmpt.mm"
include "cr.mm"
include "wceq.mm"
include "a1i.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "wcel.mm"
include "nn0ex.mm"
include "mptex.mm"
include "fvmptd.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "ovexd.mm"

theorem knoppcnlem1
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  assume knoppcnlem1.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcnlem1.2: |- ( ph -> A e. RR )
  assume knoppcnlem1.3: |- ( ph -> M e. NN0 )

  disjoint A n
  disjoint A y
  disjoint n y
  disjoint C n
  disjoint C y
  disjoint M n
  disjoint N n
  disjoint N y
  disjoint T n
  disjoint T y
  disjoint ph y
  disjoint n ph
  assert |- ( ph -> ( ( F ` A ) ` M ) = ( ( C ^ M ) x. ( T ` ( ( ( 2 x. N ) ^ M ) x. A ) ) ) )

  proof
    wph
    vn
    cM
    cC
    vn
    cv
    #
    cexp
    co
    #
    c2
    cN
    cmul
    co
    #
    @0
    cexp
    co
    #
    cA
    cmul
    co
    #
    cT
    cfv
    #
    cmul
    co
    #
    cC
    cM
    cexp
    co
    #
    @2
    cM
    cexp
    co
    #
    cA
    cmul
    co
    #
    cT
    cfv
    #
    cmul
    co
    #
    cn0
    cA
    cF
    cfv
    cvv
    wph
    vy
    cA
    vn
    cn0
    @1
    @3
    vy
    cv
    #
    cmul
    co
    #
    cT
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    vn
    cn0
    @6
    cmpt
    #
    cr
    cF
    cvv
    cF
    vy
    cr
    @16
    cmpt
    wceq
    wph
    knoppcnlem1.f
    a1i
    @12
    cA
    wceq
    #
    @16
    @17
    wceq
    wph
    @18
    vn
    cn0
    @15
    @6
    @18
    @14
    @5
    @1
    cmul
    @18
    @13
    @4
    cT
    @12
    cA
    @3
    cmul
    oveq2
    fveq2d
    oveq2d
    mpteq2dv
    adantl
    knoppcnlem1.2
    @17
    cvv
    wcel
    wph
    vn
    cn0
    @6
    nn0ex
    mptex
    a1i
    fvmptd
    @0
    cM
    wceq
    #
    @6
    @11
    wceq
    wph
    @19
    @1
    @7
    @5
    @10
    cmul
    @0
    cM
    cC
    cexp
    oveq2
    @19
    @4
    @9
    cT
    @19
    @3
    @8
    cA
    cmul
    @0
    cM
    @2
    cexp
    oveq2
    oveq1d
    fveq2d
    oveq12d
    adantl
    knoppcnlem1.3
    wph
    @7
    @10
    cmul
    ovexd
    fvmptd
end
