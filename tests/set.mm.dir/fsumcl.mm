include "cc.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "addcl.mm"
include "adantl.mm"
include "0cnd.mm"
include "fsumcllem.mm"

theorem fsumcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fsumcl.1: |- ( ph -> A e. Fin )
  assume fsumcl.2: |- ( ( ph /\ k e. A ) -> B e. CC )

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
  assert |- ( ph -> sum_ k e. A B e. CC )

  proof
    wph
    vx
    vy
    cA
    cB
    cc
    vk
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    vx
    cv
    #
    cc
    wcel
    vy
    cv
    #
    cc
    wcel
    wa
    @0
    @1
    caddc
    co
    cc
    wcel
    wph
    @0
    @1
    addcl
    adantl
    fsumcl.1
    fsumcl.2
    wph
    0cnd
    fsumcllem
end
