include "wb.mm"
include "id.mm"
include "bicomd.mm"
include "biantr.mm"
include "ex.mm"
include "syl2im.mm"

theorem bitr3VD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ph <-> ch ) -> ( ps <-> ch ) ) )

  proof
    wph
    wps
    wb
    #
    wps
    wph
    wb
    #
    wph
    wch
    wb
    #
    wch
    wph
    wb
    #
    wps
    wch
    wb
    #
    @0
    wph
    wps
    @0
    id
    bicomd
    @2
    wph
    wch
    @2
    id
    bicomd
    @1
    @3
    @4
    wps
    wph
    wch
    biantr
    ex
    syl2im
end
