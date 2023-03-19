include "dfvd2i.mm"
include "eexinst01.mm"
include "dfvd1ir.mm"

theorem exinst01
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume exinst01.1: |- E. x ps
  assume exinst01.2: |- (. ph ,. ps ->. ch ).
  assume exinst01.3: |- ( ph -> A. x ph )
  assume exinst01.4: |- ( ch -> A. x ch )


  assert |- (. ph ->. ch ).

  proof
    wph
    wch
    wph
    wps
    wch
    vx
    exinst01.1
    wph
    wps
    wch
    exinst01.2
    dfvd2i
    exinst01.3
    exinst01.4
    eexinst01
    dfvd1ir
end
