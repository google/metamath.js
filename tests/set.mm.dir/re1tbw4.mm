include "wi.mm"
include "wfal.mm"
include "re1tbw3.mm"
include "re1tbw2.mm"
include "re1tbw1.mm"
include "ax-mp.mm"
include "mercolem3.mm"
include "merco2.mm"

theorem re1tbw4
  let wph: wff ph


  assert |- ( F. -> ph )

  proof
    wph
    wph
    wi
    #
    wfal
    wph
    wi
    #
    @0
    wph
    wi
    #
    wph
    wi
    #
    @0
    wph
    wph
    re1tbw3
    wph
    @2
    wi
    @3
    @0
    wi
    wph
    @0
    re1tbw2
    wph
    @2
    wph
    re1tbw1
    ax-mp
    ax-mp
    #
    @0
    @0
    @1
    wi
    #
    @4
    @1
    @1
    wi
    #
    @0
    @5
    wi
    #
    @1
    wph
    wi
    #
    @1
    wi
    #
    @1
    wi
    #
    @6
    @1
    wph
    re1tbw3
    @1
    @9
    wi
    @10
    @6
    wi
    @1
    @8
    re1tbw2
    @1
    @9
    @1
    re1tbw1
    ax-mp
    ax-mp
    @8
    @6
    wi
    @6
    @7
    wi
    wfal
    @1
    wph
    mercolem3
    @1
    wph
    wph
    @1
    @0
    @0
    merco2
    ax-mp
    ax-mp
    ax-mp
    ax-mp
end
