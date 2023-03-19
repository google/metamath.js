include "wnf.mm"
include "wi.mm"
include "wal.mm"
include "nf5r.mm"
include "alim.mm"
include "syl9.mm"
include "wex.mm"
include "19.9t.mm"
include "imbi1d.mm"
include "19.38.mm"
include "syl6bir.mm"
include "impbid.mm"

theorem 19.21tOLDOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( F/ x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) )

  proof
    wph
    vx
    wnf
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
    @0
    wph
    wph
    vx
    wal
    @1
    @2
    wph
    vx
    nf5r
    wph
    wps
    vx
    alim
    syl9
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
    19.9t
    imbi1d
    wph
    wps
    vx
    19.38
    syl6bir
    impbid
end
