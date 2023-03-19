include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "adantr.mm"
include "mpteq12dva.mm"

theorem mpteq12dv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  assume mpteq12dv.1: |- ( ph -> A = C )
  assume mpteq12dv.2: |- ( ph -> B = D )

  disjoint ph x
  disjoint x y
  disjoint ph y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  assert |- ( ph -> ( x e. A |-> B ) = ( x e. C |-> D ) )

  proof
    wph
    vx
    cA
    cB
    cC
    cD
    mpteq12dv.1
    wph
    cB
    cD
    wceq
    vx
    cv
    cA
    wcel
    mpteq12dv.2
    adantr
    mpteq12dva
end
