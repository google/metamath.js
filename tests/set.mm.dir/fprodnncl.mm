include "cn.mm"
include "cc.mm"
include "wss.mm"
include "nnsscn.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "nnmulcl.mm"
include "adantl.mm"
include "c1.mm"
include "1nn.mm"
include "fprodcllem.mm"

theorem fprodnncl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume fprodcl.1: |- ( ph -> A e. Fin )
  assume fprodnncl.2: |- ( ( ph /\ k e. A ) -> B e. NN )

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
  assert |- ( ph -> prod_ k e. A B e. NN )

  proof
    wph
    vx
    vy
    cA
    cB
    cn
    vk
    cn
    cc
    wss
    wph
    nnsscn
    a1i
    vx
    cv
    #
    cn
    wcel
    vy
    cv
    #
    cn
    wcel
    wa
    @0
    @1
    cmul
    co
    cn
    wcel
    wph
    @0
    @1
    nnmulcl
    adantl
    fprodcl.1
    fprodnncl.2
    c1
    cn
    wcel
    wph
    1nn
    a1i
    fprodcllem
end
