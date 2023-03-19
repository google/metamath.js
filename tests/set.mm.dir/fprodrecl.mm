include "cr.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "remulcl.mm"
include "adantl.mm"
include "1red.mm"
include "fprodcllem.mm"

theorem fprodrecl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fprodcl.1: |- ( ph -> A e. Fin )
  assume fprodrecl.2: |- ( ( ph /\ k e. A ) -> B e. RR )

  disjoint A k
  disjoint k ph
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> prod_ k e. A B e. RR )

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
    cmul
    co
    cr
    wcel
    wph
    @0
    @1
    remulcl
    adantl
    fprodcl.1
    fprodrecl.2
    wph
    1red
    fprodcllem
end
