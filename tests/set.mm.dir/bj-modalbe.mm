include "wn.mm"
include "wal.mm"
include "wex.mm"
include "modal-b.mm"
include "df-ex.mm"
include "biimpri.mm"
include "sylg.mm"

theorem bj-modalbe
  let wph: wff ph
  let vx: setvar x


  assert |- ( ph -> A. x E. x ph )

  proof
    wph
    wph
    wn
    vx
    wal
    wn
    #
    wph
    vx
    wex
    #
    vx
    wph
    vx
    modal-b
    @1
    @0
    wph
    vx
    df-ex
    biimpri
    sylg
end
