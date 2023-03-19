include "wal.mm"
include "wi.mm"
include "wvd1.mm"
include "dfvd1imp.mm"
include "ax-mp.mm"
include "alrimiv.mm"
include "dfvd1impr.mm"

theorem gen11
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume gen11.1: |- (. ph ->. ps ).

  disjoint ph x
  assert |- (. ph ->. A. x ps ).

  proof
    wph
    wps
    vx
    wal
    #
    wi
    wph
    @0
    wvd1
    wph
    wps
    vx
    wph
    wps
    wvd1
    wph
    wps
    wi
    gen11.1
    wph
    wps
    dfvd1imp
    ax-mp
    alrimiv
    wph
    @0
    dfvd1impr
    ax-mp
end
