include "wb.mm"
include "ibibr.mm"
include "pm5.74ri.mm"
include "ax-mp.mm"

theorem tbt
  let wph: wff ph
  let wps: wff ps
  assume tbt.1: |- ph


  assert |- ( ps <-> ( ps <-> ph ) )

  proof
    wph
    wps
    wps
    wph
    wb
    #
    wb
    tbt.1
    wph
    wps
    @0
    wph
    wps
    ibibr
    pm5.74ri
    ax-mp
end
