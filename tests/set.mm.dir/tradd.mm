include "wtru.mm"
include "wa.mm"
include "truan.mm"
include "bitr4i.mm"

theorem tradd
  let wph: wff ph
  let wps: wff ps
  assume tradd.1: |- ( ph <-> ps )


  assert |- ( ph <-> ( T. /\ ps ) )

  proof
    wph
    wps
    wtru
    wps
    wa
    tradd.1
    wps
    truan
    bitr4i
end
