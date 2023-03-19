include "wf1o.mm"
include "ccnv.mm"
include "cmpt.mm"
include "wceq.mm"
include "f1ocnv2d.mm"
include "simpld.mm"

theorem f1o2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume f1od.1: |- F = ( x e. A |-> C )
  assume f1o2d.2: |- ( ( ph /\ x e. A ) -> C e. B )
  assume f1o2d.3: |- ( ( ph /\ y e. B ) -> D e. A )
  assume f1o2d.4: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( x = D <-> y = C ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> F : A -1-1-onto-> B )

  proof
    wph
    cA
    cB
    cF
    wf1o
    cF
    ccnv
    vy
    cB
    cD
    cmpt
    wceq
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cF
    f1od.1
    f1o2d.2
    f1o2d.3
    f1o2d.4
    f1ocnv2d
    simpld
end
