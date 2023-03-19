include "cvv.mm"
include "wcel.mm"
include "cmpt.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "eqid.mm"
include "cv.mm"
include "imp.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "f1o2d.mm"
include "f1oen2g.mm"
include "syl3anc.mm"

theorem en3d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume en3d.1: |- ( ph -> A e. _V )
  assume en3d.2: |- ( ph -> B e. _V )
  assume en3d.3: |- ( ph -> ( x e. A -> C e. B ) )
  assume en3d.4: |- ( ph -> ( y e. B -> D e. A ) )
  assume en3d.5: |- ( ph -> ( ( x e. A /\ y e. B ) -> ( x = D <-> y = C ) ) )

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
    en3d.1
    en3d.2
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    @0
    @0
    eqid
    wph
    vx
    cv
    #
    cA
    wcel
    #
    cC
    cB
    wcel
    en3d.3
    imp
    wph
    vy
    cv
    #
    cB
    wcel
    #
    cD
    cA
    wcel
    en3d.4
    imp
    wph
    @2
    @4
    wa
    @1
    cD
    wceq
    @3
    cC
    wceq
    wb
    en3d.5
    imp
    f1o2d
    cA
    cB
    @0
    cvv
    cvv
    f1oen2g
    syl3anc
end
