include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "impexp.mm"
include "df-or.mm"
include "imbi2i.mm"
include "bitr4i.mm"

theorem pm5.6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( ps \/ ch ) ) )

  proof
    wph
    wps
    wn
    #
    wa
    wch
    wi
    wph
    @0
    wch
    wi
    #
    wi
    wph
    wps
    wch
    wo
    #
    wi
    wph
    @0
    wch
    impexp
    @2
    @1
    wph
    wps
    wch
    df-or
    imbi2i
    bitr4i
end
