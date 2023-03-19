include "wb.mm"
include "wi.mm"
include "wa.mm"
include "dfbi2.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"

theorem biimpexp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph <-> ps ) -> ch ) <-> ( ( ph -> ps ) -> ( ( ps -> ph ) -> ch ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wi
    wph
    wps
    wi
    #
    wps
    wph
    wi
    #
    wa
    #
    wch
    wi
    @1
    @2
    wch
    wi
    wi
    @0
    @3
    wch
    wph
    wps
    dfbi2
    imbi1i
    @1
    @2
    wch
    impexp
    bitri
end
