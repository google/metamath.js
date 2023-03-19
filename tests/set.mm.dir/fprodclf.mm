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
include "c1.mm"
include "ax-1cn.mm"
include "fprodcllemf.mm"

theorem fprodclf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fprodclf.kph: |- F/ k ph
  assume fprodclf.a: |- ( ph -> A e. Fin )
  assume fprodclf.b: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
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
    fprodclf.kph
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
    fprodclf.a
    fprodclf.b
    c1
    cc
    wcel
    wph
    ax-1cn
    a1i
    fprodcllemf
end
