include "cr.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "readdcl.mm"
include "adantl.mm"
include "0red.mm"
include "fsumcllem.mm"

theorem fsumrecl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fsumcl.1: |- ( ph -> A e. Fin )
  assume fsumrecl.2: |- ( ( ph /\ k e. A ) -> B e. RR )

  disjoint A k
  disjoint k ph
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> sum_ k e. A B e. RR )

  proof
    wph
    vx
    vy
    cA
    cB
    cr
    vk
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    vx
    cv
    #
    cr
    wcel
    vy
    cv
    #
    cr
    wcel
    wa
    @0
    @1
    caddc
    co
    cr
    wcel
    wph
    @0
    @1
    readdcl
    adantl
    fsumcl.1
    fsumrecl.2
    wph
    0red
    fsumcllem
end
