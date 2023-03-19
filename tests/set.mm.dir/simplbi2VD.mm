include "wa.mm"
include "wi.mm"
include "wb.mm"
include "biimpr.mm"
include "e0a.mm"
include "pm3.3.mm"

theorem simplbi2VD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm3.26bi2VD.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ps -> ( ch -> ph ) )

  proof
    wps
    wch
    wa
    #
    wph
    wi
    #
    wps
    wch
    wph
    wi
    wi
    wph
    @0
    wb
    @1
    pm3.26bi2VD.1
    wph
    @0
    biimpr
    e0a
    wps
    wch
    wph
    pm3.3
    e0a
end
