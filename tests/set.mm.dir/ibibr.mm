include "wb.mm"
include "pm5.501.mm"
include "bicom.mm"
include "syl6bb.mm"
include "pm5.74i.mm"

theorem ibibr
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) )

  proof
    wph
    wps
    wps
    wph
    wb
    #
    wph
    wps
    wph
    wps
    wb
    @0
    wph
    wps
    pm5.501
    wph
    wps
    bicom
    syl6bb
    pm5.74i
end
