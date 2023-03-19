include "wtru.mm"
include "tru.mm"
include "ax-mp.mm"

theorem trud
  param wph: wff ph
  assume trud.1: |- ( T. -> ph )


  assert |- ph

  proof
    wtru
    wph
    tru
    trud.1
    ax-mp
end
