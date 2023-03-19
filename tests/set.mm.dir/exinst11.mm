include "wex.mm"
include "in1.mm"
include "dfvd2i.mm"
include "eexinst11.mm"
include "dfvd1ir.mm"

theorem exinst11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume exinst11.1: |- (. ph ->. E. x ps ).
  assume exinst11.2: |- (. ph ,. ps ->. ch ).
  assume exinst11.3: |- ( ph -> A. x ph )
  assume exinst11.4: |- ( ch -> A. x ch )


  assert |- (. ph ->. ch ).

  proof
    wph
    wch
    wph
    wps
    wch
    vx
    wph
    wps
    vx
    wex
    exinst11.1
    in1
    wph
    wps
    wch
    exinst11.2
    dfvd2i
    exinst11.3
    exinst11.4
    eexinst11
    dfvd1ir
end
