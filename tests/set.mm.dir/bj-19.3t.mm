include "wal.mm"
include "wi.mm"
include "sp.mm"
include "id.mm"
include "impbid2.mm"

theorem bj-19.3t
  let wph: wff ph
  let vx: setvar x


  assert |- ( ( ph -> A. x ph ) -> ( A. x ph <-> ph ) )

  proof
    wph
    wph
    vx
    wal
    #
    wi
    #
    @0
    wph
    wph
    vx
    sp
    @1
    id
    impbid2
end
