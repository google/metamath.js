include "wb.mm"
include "wtru.mm"
include "wfal.mm"
include "wif.mm"
include "ax-frege52a.mm"
include "ifpid2.mm"
include "3imtr4g.mm"

theorem frege52aid
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) -> ( ph -> ps ) )

  proof
    wph
    wps
    wb
    wph
    wtru
    wfal
    wif
    wps
    wtru
    wfal
    wif
    wph
    wps
    wph
    wps
    wfal
    wtru
    ax-frege52a
    wph
    ifpid2
    wps
    ifpid2
    3imtr4g
end
