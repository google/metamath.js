include "wi.mm"
include "ax-1.mm"
include "ax-2.mm"
include "ax-mp.mm"

theorem idALT
  let wph: wff ph


  assert |- ( ph -> ph )

  proof
    wph
    wph
    wph
    wi
    #
    wi
    #
    @0
    wph
    wph
    ax-1
    wph
    @0
    wph
    wi
    wi
    @1
    @0
    wi
    wph
    @0
    ax-1
    wph
    @0
    wph
    ax-2
    ax-mp
    ax-mp
end
