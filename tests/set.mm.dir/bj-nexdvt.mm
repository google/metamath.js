include "wnf.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "nfv.mm"
include "bj-nexdt.mm"
include "ax-mp.mm"

theorem bj-nexdvt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
  assert |- ( A. x ( ph -> -. ps ) -> ( ph -> -. E. x ps ) )

  proof
    wph
    vx
    wnf
    wph
    wps
    wn
    wi
    vx
    wal
    wph
    wps
    vx
    wex
    wn
    wi
    wi
    wph
    vx
    nfv
    wph
    wps
    vx
    bj-nexdt
    ax-mp
end
