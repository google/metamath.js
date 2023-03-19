include "wex.mm"
include "wi.mm"
include "wal.mm"
include "19.2.mm"
include "imim1i.mm"
include "19.35.mm"
include "sylibr.mm"

theorem 19.39
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( E. x ph -> E. x ps ) -> E. x ( ph -> ps ) )

  proof
    wph
    vx
    wex
    #
    wps
    vx
    wex
    #
    wi
    wph
    vx
    wal
    #
    @1
    wi
    wph
    wps
    wi
    vx
    wex
    @2
    @0
    @1
    wph
    vx
    19.2
    imim1i
    wph
    wps
    vx
    19.35
    sylibr
end
