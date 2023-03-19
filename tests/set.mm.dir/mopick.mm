include "wmo.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "weq.mm"
include "wal.mm"
include "mo2v.mm"
include "sp.mm"
include "pm3.45.mm"
include "aleximi.mm"
include "sb56.mm"
include "sylbi.mm"
include "syl6.mm"
include "syl5d.mm"
include "exlimiv.mm"
include "imp.mm"

theorem mopick
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( E* x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) )

  proof
    wph
    vx
    wmo
    #
    wph
    wps
    wa
    #
    vx
    wex
    #
    wph
    wps
    wi
    #
    @0
    wph
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    vy
    wex
    @2
    @3
    wi
    #
    wph
    vx
    vy
    mo2v
    @6
    @7
    vy
    @6
    wph
    @4
    @2
    wps
    @5
    vx
    sp
    @6
    @2
    @4
    wps
    wa
    #
    vx
    wex
    #
    @4
    wps
    wi
    #
    @5
    @1
    @8
    vx
    wph
    @4
    wps
    pm3.45
    aleximi
    @9
    @10
    vx
    wal
    @10
    wps
    vx
    vy
    sb56
    @10
    vx
    sp
    sylbi
    syl6
    syl5d
    exlimiv
    sylbi
    imp
end
