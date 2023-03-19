include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "biimpd.mm"
include "impancom.mm"
include "mpd.mm"
include "biimprd.mm"
include "impbida.mm"
include "eqrdv.mm"

theorem eqrdav
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqrdav.1: |- ( ( ph /\ x e. A ) -> x e. C )
  assume eqrdav.2: |- ( ( ph /\ x e. B ) -> x e. C )
  assume eqrdav.3: |- ( ( ph /\ x e. C ) -> ( x e. A <-> x e. B ) )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> A = B )

  proof
    wph
    vx
    cA
    cB
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wph
    @1
    wa
    @0
    cC
    wcel
    #
    @2
    eqrdav.1
    wph
    @3
    @1
    @2
    wph
    @3
    wa
    #
    @1
    @2
    eqrdav.3
    biimpd
    impancom
    mpd
    wph
    @2
    wa
    @3
    @1
    eqrdav.2
    wph
    @3
    @2
    @1
    @4
    @1
    @2
    eqrdav.3
    biimprd
    impancom
    mpd
    impbida
    eqrdv
end
