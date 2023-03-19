include "wb.mm"
include "wn.mm"
include "xor3.mm"
include "con2bi.mm"
include "bicom.mm"
include "3bitrri.mm"

theorem nbbn
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph <-> ps ) <-> -. ( ph <-> ps ) )

  proof
    wph
    wps
    wb
    wn
    wph
    wps
    wn
    wb
    wps
    wph
    wn
    #
    wb
    @0
    wps
    wb
    wph
    wps
    xor3
    wph
    wps
    con2bi
    wps
    @0
    bicom
    3bitrri
end
