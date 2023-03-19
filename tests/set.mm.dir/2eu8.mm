include "wex.mm"
include "weu.mm"
include "wa.mm"
include "2eu2.mm"
include "pm5.32i.mm"
include "nfeu1.mm"
include "nfeu.mm"
include "euan.mm"
include "ancom.mm"
include "eubii.mm"
include "nfe1.mm"
include "3bitri.mm"
include "3bitr4ri.mm"
include "2eu7.mm"
include "3bitr3ri.mm"

theorem 2eu8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( E! x E! y ( E. x ph /\ E. y ph ) <-> E! x E! y ( E! x ph /\ E. y ph ) )

  proof
    wph
    vy
    wex
    #
    vx
    weu
    #
    wph
    vx
    weu
    #
    vy
    weu
    #
    wa
    #
    @1
    wph
    vx
    wex
    #
    vy
    weu
    #
    wa
    @2
    @0
    wa
    #
    vy
    weu
    #
    vx
    weu
    #
    @5
    @0
    wa
    vy
    weu
    vx
    weu
    @1
    @3
    @6
    wph
    vy
    vx
    2eu2
    pm5.32i
    @3
    @0
    wa
    #
    vx
    weu
    @3
    @1
    wa
    @9
    @4
    @3
    @0
    vx
    @2
    vx
    vy
    wph
    vx
    nfeu1
    nfeu
    euan
    @8
    @10
    vx
    @8
    @0
    @2
    wa
    #
    vy
    weu
    @0
    @3
    wa
    @10
    @7
    @11
    vy
    @2
    @0
    ancom
    eubii
    @0
    @2
    vy
    wph
    vy
    nfe1
    euan
    @0
    @3
    ancom
    3bitri
    eubii
    @1
    @3
    ancom
    3bitr4ri
    wph
    vx
    vy
    2eu7
    3bitr3ri
end
