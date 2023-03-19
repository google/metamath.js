include "wa.mm"
include "wb.mm"
include "biimpr.mm"
include "expcomd.mm"

theorem simplbi2comt
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps -> ph ) ) )

  proof
    wph
    wps
    wch
    wa
    #
    wb
    wps
    wch
    wph
    wph
    @0
    biimpr
    expcomd
end
