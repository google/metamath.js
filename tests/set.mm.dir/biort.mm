include "wo.mm"
include "orc.mm"
include "ax-1.mm"
include "impbid2.mm"

theorem biort
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ph <-> ( ph \/ ps ) ) )

  proof
    wph
    wph
    wph
    wps
    wo
    #
    wph
    wps
    orc
    wph
    @0
    ax-1
    impbid2
end
