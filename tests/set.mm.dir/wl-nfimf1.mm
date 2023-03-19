include "wal.mm"
include "wi.mm"
include "nfa1.mm"
include "wb.mm"
include "pm5.5.mm"
include "sps.mm"
include "nfbidf.mm"

theorem wl-nfimf1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ph -> ( F/ x ( ph -> ps ) <-> F/ x ps ) )

  proof
    wph
    vx
    wal
    wph
    wps
    wi
    #
    wps
    vx
    wph
    vx
    nfa1
    wph
    @0
    wps
    wb
    vx
    wph
    wps
    pm5.5
    sps
    nfbidf
end
