include "wb.mm"
include "id.mm"
include "syl6bb.mm"
include "syl6bbr.mm"
include "impbii.mm"

theorem bibi2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bibi2i.1: |- ( ph <-> ps )


  assert |- ( ( ch <-> ph ) <-> ( ch <-> ps ) )

  proof
    wch
    wph
    wb
    #
    wch
    wps
    wb
    #
    @0
    wch
    wph
    wps
    @0
    id
    bibi2i.1
    syl6bb
    @1
    wch
    wps
    wph
    @1
    id
    bibi2i.1
    syl6bbr
    impbii
end
