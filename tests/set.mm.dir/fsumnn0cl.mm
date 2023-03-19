include "cn0.mm"
include "cc.mm"
include "wss.mm"
include "nn0sscn.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "nn0addcl.mm"
include "adantl.mm"
include "cc0.mm"
include "0nn0.mm"
include "fsumcllem.mm"

theorem fsumnn0cl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fsumcl.1: |- ( ph -> A e. Fin )
  assume fsumnn0cl.2: |- ( ( ph /\ k e. A ) -> B e. NN0 )

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
  assert |- ( ph -> sum_ k e. A B e. NN0 )

  proof
    wph
    vx
    vy
    cA
    cB
    cn0
    vk
    cn0
    cc
    wss
    wph
    nn0sscn
    a1i
    vx
    cv
    #
    cn0
    wcel
    vy
    cv
    #
    cn0
    wcel
    wa
    @0
    @1
    caddc
    co
    cn0
    wcel
    wph
    @0
    @1
    nn0addcl
    adantl
    fsumcl.1
    fsumnn0cl.2
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    fsumcllem
end
