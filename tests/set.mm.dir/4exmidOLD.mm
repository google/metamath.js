include "wb.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "exmid.mm"
include "dfbi3.mm"
include "xor.mm"
include "orbi12i.mm"
include "mpbi.mm"

theorem 4exmidOLD
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) \/ ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) )

  proof
    wph
    wps
    wb
    #
    @0
    wn
    #
    wo
    wph
    wps
    wa
    wph
    wn
    #
    wps
    wn
    #
    wa
    wo
    #
    wph
    @3
    wa
    wps
    @2
    wa
    wo
    #
    wo
    @0
    exmid
    @0
    @4
    @1
    @5
    wph
    wps
    dfbi3
    wph
    wps
    xor
    orbi12i
    mpbi
end
