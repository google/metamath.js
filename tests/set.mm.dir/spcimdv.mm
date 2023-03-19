include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "ex.mm"
include "alrimiv.mm"
include "nfv.mm"
include "nfcv.mm"
include "spcimgft.mm"
include "sylc.mm"

theorem spcimdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume spcimdv.1: |- ( ph -> A e. B )
  assume spcimdv.2: |- ( ( ph /\ x = A ) -> ( ps -> ch ) )

  disjoint A x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( A. x ps -> ch ) )

  proof
    wph
    vx
    cv
    cA
    wceq
    #
    wps
    wch
    wi
    #
    wi
    #
    vx
    wal
    cA
    cB
    wcel
    wps
    vx
    wal
    wch
    wi
    wph
    @2
    vx
    wph
    @0
    @1
    spcimdv.2
    ex
    alrimiv
    spcimdv.1
    wps
    wch
    vx
    cA
    cB
    wch
    vx
    nfv
    vx
    cA
    nfcv
    spcimgft
    sylc
end
