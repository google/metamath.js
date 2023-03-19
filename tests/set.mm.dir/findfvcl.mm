include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "c0.mm"
include "csuc.mm"
include "fveleq.mm"
include "com.mm"
include "a2d.mm"
include "finds.mm"

theorem findfvcl
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cF: class F
  let vx: setvar x
  assume findfvcl.1: |- ( ph -> ( F ` (/) ) e. P )
  assume findfvcl.2: |- ( y e. _om -> ( ph -> ( ( F ` y ) e. P -> ( F ` suc y ) e. P ) ) )

  disjoint F y
  disjoint P y
  disjoint ph y
  disjoint F x
  disjoint x y
  disjoint P x
  disjoint ph x
  disjoint A x
  assert |- ( A e. _om -> ( ph -> ( F ` A ) e. P ) )

  proof
    wph
    vx
    cv
    #
    cF
    cfv
    cP
    wcel
    wi
    wph
    c0
    cF
    cfv
    cP
    wcel
    wi
    wph
    vy
    cv
    #
    cF
    cfv
    cP
    wcel
    #
    wi
    wph
    @1
    csuc
    #
    cF
    cfv
    cP
    wcel
    #
    wi
    wph
    cA
    cF
    cfv
    cP
    wcel
    wi
    vx
    vy
    cA
    wph
    @0
    c0
    cP
    cF
    fveleq
    wph
    @0
    @1
    cP
    cF
    fveleq
    wph
    @0
    @3
    cP
    cF
    fveleq
    wph
    @0
    cA
    cP
    cF
    fveleq
    findfvcl.1
    @1
    com
    wcel
    wph
    @2
    @4
    findfvcl.2
    a2d
    finds
end
