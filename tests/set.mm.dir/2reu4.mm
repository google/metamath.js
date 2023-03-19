include "wrex.mm"
include "wreu.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "reurex.mm"
include "rexn0.mm"
include "syl.mm"
include "anim12i.mm"
include "cv.mm"
include "wcel.mm"
include "ne0i.mm"
include "a1d.mm"
include "rexlimivv.mm"
include "adantr.mm"
include "2reu4a.mm"
include "pm5.21nii.mm"

theorem 2reu4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint w z
  disjoint ph z
  disjoint ph w
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint k x
  assert |- ( ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) <-> ( E. x e. A E. y e. B ph /\ E. z e. A E. w e. B A. x e. A A. y e. B ( ph -> ( x = z /\ y = w ) ) ) )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    wrex
    #
    vy
    cB
    wreu
    #
    wa
    cA
    c0
    wne
    #
    cB
    c0
    wne
    #
    wa
    #
    @0
    vx
    cA
    wrex
    #
    wph
    vx
    vz
    weq
    vy
    vw
    weq
    wa
    wi
    vy
    cB
    wral
    vx
    cA
    wral
    vw
    cB
    wrex
    vz
    cA
    wrex
    #
    wa
    @1
    @4
    @3
    @5
    @1
    @7
    @4
    @0
    vx
    cA
    reurex
    @0
    vx
    cA
    rexn0
    syl
    @3
    @2
    vy
    cB
    wrex
    @5
    @2
    vy
    cB
    reurex
    @2
    vy
    cB
    rexn0
    syl
    anim12i
    @7
    @6
    @8
    wph
    @6
    vx
    vy
    cA
    cB
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    @6
    wph
    @10
    @4
    @12
    @5
    cA
    @9
    ne0i
    cB
    @11
    ne0i
    anim12i
    a1d
    rexlimivv
    adantr
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    2reu4a
    pm5.21nii
end
