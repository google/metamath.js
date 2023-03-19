include "wa.mm"
include "wb.mm"
include "wi.mm"
include "ancom.mm"
include "imbi1.mm"
include "e0a.mm"

theorem ancomstVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps /\ ph ) -> ch ) )

  proof
    wph
    wps
    wa
    #
    wps
    wph
    wa
    #
    wb
    @0
    wch
    wi
    @1
    wch
    wi
    wb
    wph
    wps
    ancom
    @0
    @1
    wch
    imbi1
    e0a
end
