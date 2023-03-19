include "cz.mm"
include "cc.mm"
include "wss.mm"
include "zsscn.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "zmulcl.mm"
include "adantl.mm"
include "1zzd.mm"
include "fprodcllem.mm"

theorem fprodzcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fprodcl.1: |- ( ph -> A e. Fin )
  assume fprodzcl.2: |- ( ( ph /\ k e. A ) -> B e. ZZ )

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
  assert |- ( ph -> prod_ k e. A B e. ZZ )

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
    cmul
    co
    cz
    wcel
    wph
    @0
    @1
    zmulcl
    adantl
    fprodcl.1
    fprodzcl.2
    wph
    1zzd
    fprodcllem
end
