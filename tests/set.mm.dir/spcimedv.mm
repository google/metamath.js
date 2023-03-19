include "wn.mm"
include "wal.mm"
include "wex.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "con3d.mm"
include "spcimdv.mm"
include "con2d.mm"
include "df-ex.mm"
include "syl6ibr.mm"

theorem spcimedv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume spcimdv.1: |- ( ph -> A e. B )
  assume spcimedv.2: |- ( ( ph /\ x = A ) -> ( ch -> ps ) )

  disjoint A x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( ch -> E. x ps ) )

  proof
    wph
    wch
    wps
    wn
    #
    vx
    wal
    #
    wn
    wps
    vx
    wex
    wph
    @1
    wch
    wph
    @0
    wch
    wn
    vx
    cA
    cB
    spcimdv.1
    wph
    vx
    cv
    cA
    wceq
    wa
    wch
    wps
    spcimedv.2
    con3d
    spcimdv
    con2d
    wps
    vx
    df-ex
    syl6ibr
end
