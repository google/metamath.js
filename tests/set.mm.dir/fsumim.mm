include "cim.mm"
include "cc.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "imf.mm"
include "ax-resscn.mm"
include "fss.mm"
include "mp2an.mm"
include "cv.mm"
include "imadd.mm"
include "fsumrelem.mm"

theorem fsumim
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
  assert |- ( ph -> ( Im ` sum_ k e. A B ) = sum_ k e. A ( Im ` B ) )

  proof
    wph
    vx
    vy
    cA
    cB
    vk
    cim
    fsumre.1
    fsumre.2
    cc
    cr
    cim
    wf
    cr
    cc
    wss
    cc
    cc
    cim
    wf
    imf
    ax-resscn
    cc
    cr
    cc
    cim
    fss
    mp2an
    vx
    cv
    vy
    cv
    imadd
    fsumrelem
end
