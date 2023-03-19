include "wb.mm"
include "bicom.mm"
include "bibi1i.mm"
include "biass.mm"
include "bitri.mm"
include "mpbi.mm"
include "bitr4i.mm"

theorem biluk
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) <-> ( ( ch <-> ps ) <-> ( ph <-> ch ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wps
    wph
    wch
    wb
    #
    wb
    #
    wb
    #
    wch
    wps
    wb
    @1
    wb
    @0
    wch
    wb
    #
    @2
    wb
    @0
    @3
    wb
    @4
    wps
    wph
    wb
    #
    wch
    wb
    @2
    @0
    @5
    wch
    wph
    wps
    bicom
    bibi1i
    wps
    wph
    wch
    biass
    bitri
    @0
    wch
    @2
    biass
    mpbi
    wch
    wps
    @1
    biass
    bitr4i
end
