include "wal.mm"
include "in1.mm"
include "alrimih.mm"
include "dfvd1ir.mm"

theorem gen11nv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume gen11nv.1: |- ( ph -> A. x ph )
  assume gen11nv.2: |- (. ph ->. ps ).


  assert |- (. ph ->. A. x ps ).

  proof
    wph
    wps
    vx
    wal
    wph
    wps
    vx
    gen11nv.1
    wph
    wps
    gen11nv.2
    in1
    alrimih
    dfvd1ir
end
