include "wif.mm"
include "wn.mm"
include "ifpnot23.mm"
include "bicomi.mm"

theorem ifpnotnotb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( if- ( ph , -. ps , -. ch ) <-> -. if- ( ph , ps , ch ) )

  proof
    wph
    wps
    wch
    wif
    wn
    wph
    wps
    wn
    wch
    wn
    wif
    wph
    wps
    wch
    ifpnot23
    bicomi
end
