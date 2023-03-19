include "wal.mm"
include "wi.mm"
include "wex.mm"
include "19.9ht.mm"
include "19.8a.mm"
include "impbid1.mm"

theorem bj-19.9htbi
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ( ph -> A. x ph ) -> ( E. x ph <-> ph ) )

  proof
    wph
    wph
    vx
    wal
    wi
    vx
    wal
    wph
    vx
    wex
    wph
    wph
    vx
    19.9ht
    wph
    vx
    19.8a
    impbid1
end
