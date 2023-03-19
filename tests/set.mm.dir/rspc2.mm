include "wcel.mm"
include "wral.mm"
include "nfcv.mm"
include "nfral.mm"
include "cv.mm"
include "wceq.mm"
include "ralbidv.mm"
include "rspc.mm"
include "sylan9.mm"

theorem rspc2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rspc2.1: |- F/ x ch
  assume rspc2.2: |- F/ y ps
  assume rspc2.3: |- ( x = A -> ( ph <-> ch ) )
  assume rspc2.4: |- ( y = B -> ( ch <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint D x
  disjoint D y
  assert |- ( ( A e. C /\ B e. D ) -> ( A. x e. C A. y e. D ph -> ps ) )

  proof
    cA
    cC
    wcel
    wph
    vy
    cD
    wral
    #
    vx
    cC
    wral
    wch
    vy
    cD
    wral
    #
    cB
    cD
    wcel
    wps
    @0
    @1
    vx
    cA
    cC
    wch
    vx
    vy
    cD
    vx
    cD
    nfcv
    rspc2.1
    nfral
    vx
    cv
    cA
    wceq
    wph
    wch
    vy
    cD
    rspc2.3
    ralbidv
    rspc
    wch
    wps
    vy
    cB
    cD
    rspc2.2
    rspc2.4
    rspc
    sylan9
end
