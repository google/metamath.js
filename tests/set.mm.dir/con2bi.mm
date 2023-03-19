include "wn.mm"
include "wb.mm"
include "notbi.mm"
include "notnotb.mm"
include "bibi2i.mm"
include "bicom.mm"
include "3bitr2i.mm"

theorem con2bi
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> -. ps ) <-> ( ps <-> -. ph ) )

  proof
    wph
    wps
    wn
    #
    wb
    wph
    wn
    #
    @0
    wn
    #
    wb
    @1
    wps
    wb
    wps
    @1
    wb
    wph
    @0
    notbi
    wps
    @2
    @1
    wps
    notnotb
    bibi2i
    @1
    wps
    bicom
    3bitr2i
end
