include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "wex.mm"
include "nf5.mm"
include "nf6.mm"
include "bitr3i.mm"

theorem xfree
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x ( ph -> A. x ph ) <-> A. x ( E. x ph -> ph ) )

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
    wnf
    wph
    vx
    wex
    wph
    wi
    vx
    wal
    wph
    vx
    nf5
    wph
    vx
    nf6
    bitr3i
end
