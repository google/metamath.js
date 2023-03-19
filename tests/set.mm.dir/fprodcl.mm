include "cc.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "mulcl.mm"
include "adantl.mm"
include "1cnd.mm"
include "fprodcllem.mm"

theorem fprodcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fprodcl.1: |- ( ph -> A e. Fin )
  assume fprodcl.2: |- ( ( ph /\ k e. A ) -> B e. CC )

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
  assert |- ( ph -> prod_ k e. A B e. CC )

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
    cmul
    co
    cc
    wcel
    wph
    @0
    @1
    mulcl
    adantl
    fprodcl.1
    fprodcl.2
    wph
    1cnd
    fprodcllem
end
