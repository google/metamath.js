include "wb.mm"
include "wn.mm"
include "id.mm"
include "notbid.mm"
include "con4bid.mm"
include "impbii.mm"

theorem notbi
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) <-> ( -. ph <-> -. ps ) )

  proof
    wph
    wps
    wb
    #
    wph
    wn
    wps
    wn
    wb
    #
    @0
    wph
    wps
    @0
    id
    notbid
    @1
    wph
    wps
    @1
    id
    con4bid
    impbii
end
