include "cmpt.mm"
include "wf1.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "dom2lem.mm"
include "f1domg.mm"
include "syl5com.mm"

theorem dom2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vz: setvar z
  assume dom2d.1: |- ( ph -> ( x e. A -> C e. B ) )
  assume dom2d.2: |- ( ph -> ( ( x e. A /\ y e. A ) -> ( C = D <-> x = y ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  disjoint ph x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  assert |- ( ph -> ( B e. R -> A ~<_ B ) )

  proof
    wph
    cA
    cB
    vx
    cA
    cC
    cmpt
    #
    wf1
    cB
    cR
    wcel
    cA
    cB
    cdom
    wbr
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    dom2d.1
    dom2d.2
    dom2lem
    cA
    cB
    cR
    @0
    f1domg
    syl5com
end
