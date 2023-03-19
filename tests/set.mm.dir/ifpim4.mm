include "wi.mm"
include "wn.mm"
include "wif.mm"
include "wb.mm"
include "wa.mm"
include "wo.mm"
include "simpr.mm"
include "olc.mm"
include "ifpim23g.mm"
include "mpbir2an.mm"

theorem ifpim4
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> if- ( ps , ps , -. ph ) )

  proof
    wph
    wps
    wi
    wps
    wps
    wph
    wn
    wif
    wb
    wph
    wps
    wa
    wps
    wi
    wps
    wph
    wps
    wo
    wi
    wph
    wps
    simpr
    wps
    wph
    olc
    wph
    wps
    wps
    ifpim23g
    mpbir2an
end
