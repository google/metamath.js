include "wi.mm"
include "wal.mm"
include "wex.mm"
include "exim.mm"
include "19.9v.mm"
include "syl6ib.mm"
include "ax-5.mm"
include "imim2i.mm"
include "19.38.mm"
include "syl.mm"
include "impbii.mm"

theorem 19.23v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ps x
  assert |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) )

  proof
    wph
    wps
    wi
    vx
    wal
    #
    wph
    vx
    wex
    #
    wps
    wi
    #
    @0
    @1
    wps
    vx
    wex
    wps
    wph
    wps
    vx
    exim
    wps
    vx
    19.9v
    syl6ib
    @2
    @1
    wps
    vx
    wal
    #
    wi
    @0
    wps
    @3
    @1
    wps
    vx
    ax-5
    imim2i
    wph
    wps
    vx
    19.38
    syl
    impbii
end
