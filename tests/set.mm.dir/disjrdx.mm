include "cv.mm"
include "wcel.mm"
include "wrmo.mm"
include "wal.mm"
include "wdisj.mm"
include "cfv.mm"
include "wf1o.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "wa.mm"
include "wceq.mm"
include "wreu.mm"
include "f1ofveu.mm"
include "sylan.mm"
include "eqcom.mm"
include "reubii.mm"
include "sylib.mm"
include "eleq2d.mm"
include "rmoxfrd.mm"
include "bicomd.mm"
include "albidv.mm"
include "df-disj.mm"
include "3bitr4g.mm"

theorem disjrdx
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vz: setvar z
  assume disjrdx.1: |- ( ph -> F : A -1-1-onto-> C )
  assume disjrdx.2: |- ( ( ph /\ y = ( F ` x ) ) -> D = B )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint ph z
  assert |- ( ph -> ( Disj_ x e. A B <-> Disj_ y e. C D ) )

  proof
    wph
    vz
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wrmo
    #
    vz
    wal
    @0
    cD
    wcel
    #
    vy
    cC
    wrmo
    #
    vz
    wal
    vx
    cA
    cB
    wdisj
    vy
    cC
    cD
    wdisj
    wph
    @2
    @4
    vz
    wph
    @4
    @2
    wph
    @3
    @1
    vy
    vx
    vx
    cv
    #
    cF
    cfv
    #
    cC
    cA
    wph
    cA
    cC
    @5
    cF
    wph
    cA
    cC
    cF
    wf1o
    #
    cA
    cC
    cF
    wf
    disjrdx.1
    cA
    cC
    cF
    f1of
    syl
    ffvelrnda
    wph
    vy
    cv
    #
    cC
    wcel
    #
    wa
    @6
    @8
    wceq
    #
    vx
    cA
    wreu
    #
    @8
    @6
    wceq
    #
    vx
    cA
    wreu
    wph
    @7
    @9
    @11
    disjrdx.1
    vx
    cA
    cC
    @8
    cF
    f1ofveu
    sylan
    @10
    @12
    vx
    cA
    @6
    @8
    eqcom
    reubii
    sylib
    wph
    @12
    wa
    cD
    cB
    @0
    disjrdx.2
    eleq2d
    rmoxfrd
    bicomd
    albidv
    vx
    vz
    cA
    cB
    df-disj
    vy
    vz
    cC
    cD
    df-disj
    3bitr4g
end
