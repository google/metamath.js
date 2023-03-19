include "wb.mm"
include "biimpr.mm"
include "biimp.mm"
include "impbid.mm"

theorem bicom1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) -> ( ps <-> ph ) )

  proof
    wph
    wps
    wb
    wps
    wph
    wph
    wps
    biimpr
    wph
    wps
    biimp
    impbid
end
