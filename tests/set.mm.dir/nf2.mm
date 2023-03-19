include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "df-nf.mm"
include "imor.mm"
include "orcom.mm"
include "3bitri.mm"

theorem nf2
  let wph: wff ph
  let vx: setvar x


  assert |- ( F/ x ph <-> ( A. x ph \/ -. E. x ph ) )

  proof
    wph
    vx
    wnf
    wph
    vx
    wex
    #
    wph
    vx
    wal
    #
    wi
    @0
    wn
    #
    @1
    wo
    @1
    @2
    wo
    wph
    vx
    df-nf
    @0
    @1
    imor
    @2
    @1
    orcom
    3bitri
end
