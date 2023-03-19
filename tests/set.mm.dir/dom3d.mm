include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wf.mm"
include "dom2lem.mm"
include "f1f.mm"
include "syl.mm"
include "fex2.mm"
include "syl3anc.mm"
include "f1eq1.mm"
include "spcegv.mm"
include "sylc.mm"
include "wb.mm"
include "brdomg.mm"
include "mpbird.mm"

theorem dom3d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let vz: setvar z
  assume dom2d.1: |- ( ph -> ( x e. A -> C e. B ) )
  assume dom2d.2: |- ( ph -> ( ( x e. A /\ y e. A ) -> ( C = D <-> x = y ) ) )
  assume dom3d.3: |- ( ph -> A e. V )
  assume dom3d.4: |- ( ph -> B e. W )

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
  assert |- ( ph -> A ~<_ B )

  proof
    wph
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    vz
    cv
    #
    wf1
    #
    vz
    wex
    #
    wph
    vx
    cA
    cC
    cmpt
    #
    cvv
    wcel
    #
    cA
    cB
    @4
    wf1
    #
    @3
    wph
    cA
    cB
    @4
    wf
    #
    cA
    cV
    wcel
    cB
    cW
    wcel
    #
    @5
    wph
    @6
    @7
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
    #
    cA
    cB
    @4
    f1f
    syl
    dom3d.3
    dom3d.4
    cA
    cB
    @4
    cV
    cW
    fex2
    syl3anc
    @9
    @2
    @6
    vz
    @4
    cvv
    cA
    cB
    @1
    @4
    f1eq1
    spcegv
    sylc
    wph
    @8
    @0
    @3
    wb
    dom3d.4
    cA
    cB
    cW
    vz
    brdomg
    syl
    mpbird
end
