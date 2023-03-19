include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "ex.mm"
include "alrimiv.mm"
include "wex.mm"
include "bj-elissetv.mm"
include "exim.mm"
include "syl5.mm"
include "19.36v.mm"
include "syl6ib.mm"
include "sylc.mm"

theorem bj-spcimdvv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bj-spcimdvv.1: |- ( ph -> A e. B )
  assume bj-spcimdvv.2: |- ( ( ph /\ x = A ) -> ( ps -> ch ) )

  disjoint A x
  disjoint B x
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
    bj-spcimdvv.2
    ex
    alrimiv
    bj-spcimdvv.1
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
    bj-elissetv
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
