include "wn.mm"
include "wif.mm"
include "wi.mm"
include "ifpnot23c.mm"
include "ifpim4.mm"
include "xchnxbir.mm"

theorem ifpnim2
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph -> ps ) <-> if- ( ps , -. ps , ph ) )

  proof
    wps
    wps
    wph
    wn
    wif
    wps
    wps
    wn
    wph
    wif
    wph
    wps
    wi
    wps
    wps
    wph
    ifpnot23c
    wph
    wps
    ifpim4
    xchnxbir
end
