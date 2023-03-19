include "wi.mm"
include "idd.mm"
include "a1i.mm"
include "dfvd3ir.mm"

theorem idn3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- (. ph ,. ps ,. ch ->. ch ).

  proof
    wph
    wps
    wch
    wch
    wps
    wch
    wch
    wi
    wi
    wph
    wps
    wch
    idd
    a1i
    dfvd3ir
end
