include "wal.mm"
include "wi.mm"
include "wex.mm"
include "19.2.mm"
include "imim2i.mm"
include "19.35.mm"
include "sylibr.mm"

theorem 19.24
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( A. x ph -> A. x ps ) -> E. x ( ph -> ps ) )

  proof
    wph
    vx
    wal
    #
    wps
    vx
    wal
    #
    wi
    @0
    wps
    vx
    wex
    #
    wi
    wph
    wps
    wi
    vx
    wex
    @1
    @2
    @0
    wps
    vx
    19.2
    imim2i
    wph
    wps
    vx
    19.35
    sylibr
end
