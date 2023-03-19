include "idd.mm"
include "dfvd2ir.mm"

theorem idn2
  let wph: wff ph
  let wps: wff ps


  assert |- (. ph ,. ps ->. ps ).

  proof
    wph
    wps
    wps
    wph
    wps
    idd
    dfvd2ir
end
