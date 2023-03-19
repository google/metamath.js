include "wi.mm"
include "wn.mm"
include "simprim.mm"
include "simplim.mm"
include "imim1i.mm"
include "mpdi.mm"

theorem impt
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) )

  proof
    wph
    wps
    wch
    wi
    #
    wi
    wph
    wps
    wn
    #
    wi
    wn
    #
    wps
    wch
    wph
    wps
    simprim
    @2
    wph
    @0
    wph
    @1
    simplim
    imim1i
    mpdi
end
