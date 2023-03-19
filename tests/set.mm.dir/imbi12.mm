include "wb.mm"
include "wi.mm"
include "wn.mm"
include "simplim.mm"
include "simprim.mm"
include "imbi12d.mm"
include "expi.mm"

theorem imbi12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph <-> ps ) -> ( ( ch <-> th ) -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wth
    wb
    #
    wph
    wch
    wi
    wps
    wth
    wi
    wb
    @0
    @1
    wn
    #
    wi
    wn
    wph
    wps
    wch
    wth
    @0
    @2
    simplim
    @0
    @1
    simprim
    imbi12d
    expi
end
