include "wa.mm"
include "wn.mm"
include "wi.mm"
include "impexp.mm"
include "imnan.mm"
include "imbi2i.mm"
include "bitr2i.mm"

theorem nan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> -. ( ps /\ ch ) ) <-> ( ( ph /\ ps ) -> -. ch ) )

  proof
    wph
    wps
    wa
    wch
    wn
    #
    wi
    wph
    wps
    @0
    wi
    #
    wi
    wph
    wps
    wch
    wa
    wn
    #
    wi
    wph
    wps
    @0
    impexp
    @1
    @2
    wph
    wps
    wch
    imnan
    imbi2i
    bitr2i
end
