include "wnfOLD.mm"
include "wi.mm"
include "wal.mm"
include "19.21t-1OLD.mm"
include "wex.mm"
include "19.9tOLD.mm"
include "imbi1d.mm"
include "19.38.mm"
include "syl6bir.mm"
include "impbid.mm"

theorem 19.21tOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( nfOLD x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) )

  proof
    wph
    vx
    wnfOLD
    #
    wph
    wps
    wi
    vx
    wal
    #
    wph
    wps
    vx
    wal
    #
    wi
    #
    wph
    wps
    vx
    19.21t-1OLD
    @0
    @3
    wph
    vx
    wex
    #
    @2
    wi
    @1
    @0
    @4
    wph
    @2
    wph
    vx
    19.9tOLD
    imbi1d
    wph
    wps
    vx
    19.38
    syl6bir
    impbid
end
