include "wa.mm"
include "wi.mm"
include "ancomst.mm"
include "impexp.mm"
include "bitri.mm"
include "imbi2i.mm"

theorem expcomdg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <-> ( ph -> ( ch -> ( ps -> th ) ) ) )

  proof
    wps
    wch
    wa
    wth
    wi
    #
    wch
    wps
    wth
    wi
    wi
    #
    wph
    @0
    wch
    wps
    wa
    wth
    wi
    @1
    wps
    wch
    wth
    ancomst
    wch
    wps
    wth
    impexp
    bitri
    imbi2i
end
