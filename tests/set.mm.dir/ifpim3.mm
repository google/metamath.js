include "wi.mm"
include "wn.mm"
include "wif.mm"
include "wb.mm"
include "wa.mm"
include "wo.mm"
include "simpl.mm"
include "orc.mm"
include "ifpim23g.mm"
include "mpbir2an.mm"

theorem ifpim3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> if- ( ph , ps , -. ph ) )

  proof
    wph
    wps
    wi
    wph
    wps
    wph
    wn
    wif
    wb
    wph
    wps
    wa
    wph
    wi
    wph
    wph
    wps
    wo
    wi
    wph
    wps
    simpl
    wph
    wps
    orc
    wph
    wps
    wph
    ifpim23g
    mpbir2an
end
