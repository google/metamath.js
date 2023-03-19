include "wal.mm"
include "wi.mm"
include "wn.mm"
include "nf5-1.mm"
include "nfnd.mm"
include "nf5rd.mm"

theorem hbnt
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) )

  proof
    wph
    wph
    vx
    wal
    wi
    vx
    wal
    #
    wph
    wn
    vx
    @0
    wph
    vx
    wph
    vx
    nf5-1
    nfnd
    nf5rd
end
