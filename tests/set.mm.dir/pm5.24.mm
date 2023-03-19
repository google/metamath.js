include "wb.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "xor.mm"
include "dfbi3.mm"
include "xchnxbi.mm"

theorem pm5.24
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) <-> ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) )

  proof
    wph
    wps
    wb
    wph
    wps
    wn
    #
    wa
    wps
    wph
    wn
    #
    wa
    wo
    wph
    wps
    wa
    @1
    @0
    wa
    wo
    wph
    wps
    xor
    wph
    wps
    dfbi3
    xchnxbi
end
