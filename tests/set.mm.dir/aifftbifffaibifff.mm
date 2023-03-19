include "wb.mm"
include "wn.mm"
include "wfal.mm"
include "aistia.mm"
include "aisfina.mm"
include "abnotbtaxb.mm"
include "axorbtnotaiffb.mm"
include "nbfal.mm"
include "biimpi.mm"
include "ax-mp.mm"

theorem aifftbifffaibifff
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x
  assume aifftbifffaibifff.1: |- ( ph <-> T. )
  assume aifftbifffaibifff.2: |- ( ps <-> F. )


  assert |- ( ( ph <-> ps ) <-> F. )

  proof
    wph
    wps
    wb
    #
    wn
    #
    @0
    wfal
    wb
    #
    wph
    wps
    wph
    wps
    wph
    aifftbifffaibifff.1
    aistia
    wps
    aifftbifffaibifff.2
    aisfina
    abnotbtaxb
    axorbtnotaiffb
    @1
    @2
    @0
    nbfal
    biimpi
    ax-mp
end
