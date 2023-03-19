include "cz.mm"
include "cc.mm"
include "wss.mm"
include "zsscn.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "zaddcl.mm"
include "adantl.mm"
include "0zd.mm"
include "fsumcllem.mm"

theorem fsumzcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fsumcl.1: |- ( ph -> A e. Fin )
  assume fsumzcl.2: |- ( ( ph /\ k e. A ) -> B e. ZZ )

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
  assert |- ( ph -> sum_ k e. A B e. ZZ )

  proof
    wph
    vx
    vy
    cA
    cB
    cz
    vk
    cz
    cc
    wss
    wph
    zsscn
    a1i
    vx
    cv
    #
    cz
    wcel
    vy
    cv
    #
    cz
    wcel
    wa
    @0
    @1
    caddc
    co
    cz
    wcel
    wph
    @0
    @1
    zaddcl
    adantl
    fsumcl.1
    fsumzcl.2
    wph
    0zd
    fsumcllem
end
