include "wnfOLD.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wb.mm"
include "nfntOLD.mm"
include "19.21tOLD.mm"
include "syl.mm"
include "con34b.mm"
include "albii.mm"
include "eximal.mm"
include "3bitr4g.mm"

theorem 19.23tOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( nfOLD x ps -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) )

  proof
    wps
    vx
    wnfOLD
    #
    wps
    wn
    #
    wph
    wn
    #
    wi
    #
    vx
    wal
    #
    @1
    @2
    vx
    wal
    wi
    #
    wph
    wps
    wi
    #
    vx
    wal
    wph
    vx
    wex
    wps
    wi
    @0
    @1
    vx
    wnfOLD
    @4
    @5
    wb
    wps
    vx
    nfntOLD
    @1
    @2
    vx
    19.21tOLD
    syl
    @6
    @3
    vx
    wph
    wps
    con34b
    albii
    wph
    wps
    vx
    eximal
    3bitr4g
end
