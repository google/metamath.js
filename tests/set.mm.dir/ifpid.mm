include "wif.mm"
include "wb.mm"
include "ifptru.mm"
include "ifpfal.mm"
include "pm2.61i.mm"

theorem ifpid
  let wph: wff ph
  let wps: wff ps


  assert |- ( if- ( ph , ps , ps ) <-> ps )

  proof
    wph
    wph
    wps
    wps
    wif
    wps
    wb
    wph
    wps
    wps
    ifptru
    wph
    wps
    wps
    ifpfal
    pm2.61i
end
