include "wn.mm"
include "wif.mm"
include "wi.mm"
include "ifpnot23c.mm"
include "ifpim3.mm"
include "xchnxbir.mm"

theorem ifpnim1
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph -> ps ) <-> if- ( ph , -. ps , ph ) )

  proof
    wph
    wps
    wph
    wn
    wif
    wph
    wps
    wn
    wph
    wif
    wph
    wps
    wi
    wph
    wps
    wph
    ifpnot23c
    wph
    wps
    ifpim3
    xchnxbir
end
