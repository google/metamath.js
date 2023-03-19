include "wnf.mm"
include "wal.mm"
include "wn.mm"
include "wo.mm"
include "wi.mm"
include "nf3.mm"
include "df-or.mm"
include "bitri.mm"

theorem nf4
  let wph: wff ph
  let vx: setvar x


  assert |- ( F/ x ph <-> ( -. A. x ph -> A. x -. ph ) )

  proof
    wph
    vx
    wnf
    wph
    vx
    wal
    #
    wph
    wn
    vx
    wal
    #
    wo
    @0
    wn
    @1
    wi
    wph
    vx
    nf3
    @0
    @1
    df-or
    bitri
end
