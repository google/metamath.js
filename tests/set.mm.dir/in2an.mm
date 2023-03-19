include "wi.mm"
include "wa.mm"
include "dfvd2i.mm"
include "expd.mm"
include "dfvd2ir.mm"

theorem in2an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume in2an.1: |- (. ph ,. ( ps /\ ch ) ->. th ).


  assert |- (. ph ,. ps ->. ( ch -> th ) ).

  proof
    wph
    wps
    wch
    wth
    wi
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wa
    wth
    in2an.1
    dfvd2i
    expd
    dfvd2ir
end
