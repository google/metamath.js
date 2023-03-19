include "wex.mm"
include "weu.mm"
include "wa.mm"
include "nfe1.mm"
include "nfeu.mm"
include "euan.mm"
include "ancom.mm"
include "eubii.mm"
include "3bitri.mm"
include "3bitr4ri.mm"

theorem 2eu7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( E! x E. y ph /\ E! y E. x ph ) <-> E! x E! y ( E. x ph /\ E. y ph ) )

  proof
    wph
    vx
    wex
    #
    vy
    weu
    #
    wph
    vy
    wex
    #
    wa
    #
    vx
    weu
    @1
    @2
    vx
    weu
    #
    wa
    @0
    @2
    wa
    #
    vy
    weu
    #
    vx
    weu
    @4
    @1
    wa
    @1
    @2
    vx
    @0
    vx
    vy
    wph
    vx
    nfe1
    nfeu
    euan
    @6
    @3
    vx
    @6
    @2
    @0
    wa
    #
    vy
    weu
    @2
    @1
    wa
    @3
    @5
    @7
    vy
    @0
    @2
    ancom
    eubii
    @2
    @0
    vy
    wph
    vy
    nfe1
    euan
    @2
    @1
    ancom
    3bitri
    eubii
    @4
    @1
    ancom
    3bitr4ri
end
