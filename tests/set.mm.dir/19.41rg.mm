include "wal.mm"
include "wi.mm"
include "wex.mm"
include "wa.mm"
include "sp.mm"
include "pm3.21.mm"
include "a1i.mm"
include "al2imi.mm"
include "exim.mm"
include "syl6.mm"
include "syld.mm"
include "com23.mm"
include "impd.mm"

theorem 19.41rg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ps -> A. x ps ) -> ( ( E. x ph /\ ps ) -> E. x ( ph /\ ps ) ) )

  proof
    wps
    wps
    vx
    wal
    #
    wi
    #
    vx
    wal
    #
    wph
    vx
    wex
    #
    wps
    wph
    wps
    wa
    #
    vx
    wex
    #
    @2
    wps
    @3
    @5
    @2
    wps
    @0
    @3
    @5
    wi
    #
    @1
    vx
    sp
    @2
    @0
    wph
    @4
    wi
    #
    vx
    wal
    @6
    @1
    wps
    @7
    vx
    wps
    @7
    wi
    @1
    wps
    wph
    pm3.21
    a1i
    al2imi
    wph
    @4
    vx
    exim
    syl6
    syld
    com23
    impd
end
