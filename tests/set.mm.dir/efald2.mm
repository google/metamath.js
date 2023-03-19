include "wtru.mm"
include "wn.mm"
include "wfal.mm"
include "adantl.mm"
include "efald.mm"
include "trud.mm"

theorem efald2
  let wph: wff ph
  assume efald2.1: |- ( -. ph -> F. )


  assert |- ph

  proof
    wph
    wtru
    wph
    wph
    wn
    wfal
    wtru
    efald2.1
    adantl
    efald
    trud
end
