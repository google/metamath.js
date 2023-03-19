include "wi.mm"
include "wn.mm"
include "wa.mm"
include "con34b.mm"
include "imbi2i.mm"
include "impexp.mm"
include "3bitr4i.mm"

theorem pm4.14
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ -. ch ) -> -. ps ) )

  proof
    wph
    wps
    wch
    wi
    #
    wi
    wph
    wch
    wn
    #
    wps
    wn
    #
    wi
    #
    wi
    wph
    wps
    wa
    wch
    wi
    wph
    @1
    wa
    @2
    wi
    @0
    @3
    wph
    wps
    wch
    con34b
    imbi2i
    wph
    wps
    wch
    impexp
    wph
    @1
    @2
    impexp
    3bitr4i
end
