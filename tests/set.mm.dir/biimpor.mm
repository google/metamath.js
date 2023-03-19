include "wb.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "imor.mm"
include "notbinot2.mm"
include "orbi1i.mm"
include "bitri.mm"

theorem biimpor
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph <-> ps ) -> ch ) <-> ( ( -. ph <-> ps ) \/ ch ) )

  proof
    wph
    wps
    wb
    #
    wch
    wi
    @0
    wn
    #
    wch
    wo
    wph
    wn
    wps
    wb
    #
    wch
    wo
    @0
    wch
    imor
    @1
    @2
    wch
    wph
    wps
    notbinot2
    orbi1i
    bitri
end
