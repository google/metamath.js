include "ccj.mm"
include "cjf.mm"
include "cv.mm"
include "cjadd.mm"
include "fsumrelem.mm"

theorem fsumcj
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vf: setvar f
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  assume fsumre.1: |- ( ph -> A e. Fin )
  assume fsumre.2: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint k ph
  disjoint f k
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint F f
  disjoint F k
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint f ph
  disjoint m ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( * ` sum_ k e. A B ) = sum_ k e. A ( * ` B ) )

  proof
    wph
    vx
    vy
    cA
    cB
    vk
    ccj
    fsumre.1
    fsumre.2
    cjf
    vx
    cv
    vy
    cv
    cjadd
    fsumrelem
end
