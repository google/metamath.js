include "cvv.mm"
include "wcel.mm"
include "cmpt.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "eqid.mm"
include "cv.mm"
include "imp.mm"
include "f1od.mm"
include "f1oen2g.mm"
include "syl3anc.mm"

theorem en2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume en2d.1: |- ( ph -> A e. _V )
  assume en2d.2: |- ( ph -> B e. _V )
  assume en2d.3: |- ( ph -> ( x e. A -> C e. _V ) )
  assume en2d.4: |- ( ph -> ( y e. B -> D e. _V ) )
  assume en2d.5: |- ( ph -> ( ( x e. A /\ y = C ) <-> ( y e. B /\ x = D ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A ~~ B )

  proof
    wph
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    vx
    cA
    cC
    cmpt
    #
    wf1o
    cA
    cB
    cen
    wbr
    en2d.1
    en2d.2
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    @0
    cvv
    cvv
    @0
    eqid
    wph
    vx
    cv
    cA
    wcel
    cC
    cvv
    wcel
    en2d.3
    imp
    wph
    vy
    cv
    cB
    wcel
    cD
    cvv
    wcel
    en2d.4
    imp
    en2d.5
    f1od
    cA
    cB
    @0
    cvv
    cvv
    f1oen2g
    syl3anc
end
