include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "ex.mm"
include "alrimiv.mm"
include "wex.mm"
include "bj-elisset.mm"
include "exim.mm"
include "syl5.mm"
include "19.36v.mm"
include "syl6ib.mm"
include "sylc.mm"

theorem bj-spcimdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bj-spcimdv.1: |- ( ph -> A e. B )
  assume bj-spcimdv.2: |- ( ( ph /\ x = A ) -> ( ps -> ch ) )

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
    #
    cA
    cB
    wcel
    #
    wps
    vx
    wal
    wch
    wi
    #
    wph
    @2
    vx
    wph
    @0
    @1
    bj-spcimdv.2
    ex
    alrimiv
    bj-spcimdv.1
    @3
    @4
    @1
    vx
    wex
    #
    @5
    @4
    @0
    vx
    wex
    @3
    @6
    vx
    cA
    cB
    bj-elisset
    @0
    @1
    vx
    exim
    syl5
    wps
    wch
    vx
    19.36v
    syl6ib
    sylc
end
