include "cn0.mm"
include "cc.mm"
include "wss.mm"
include "nn0sscn.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "nn0mulcl.mm"
include "adantl.mm"
include "c1.mm"
include "1nn0.mm"
include "fprodcllem.mm"

theorem fprodnn0cl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fprodcl.1: |- ( ph -> A e. Fin )
  assume fprodnn0cl.2: |- ( ( ph /\ k e. A ) -> B e. NN0 )

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
  assert |- ( ph -> prod_ k e. A B e. NN0 )

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
    cmul
    co
    cn0
    wcel
    wph
    @0
    @1
    nn0mulcl
    adantl
    fprodcl.1
    fprodnn0cl.2
    c1
    cn0
    wcel
    wph
    1nn0
    a1i
    fprodcllem
end
