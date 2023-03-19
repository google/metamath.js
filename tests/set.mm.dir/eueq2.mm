include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "weu.mm"
include "notnot.mm"
include "eueq1.mm"
include "euanv.mm"
include "biimpri.mm"
include "mpan2.mm"
include "euorv.mm"
include "syl2anc.mm"
include "orcom.mm"
include "bianfd.mm"
include "orbi2d.mm"
include "syl5bb.mm"
include "eubidv.mm"
include "mpbid.mm"
include "mpdan.mm"
include "id.mm"
include "orbi1d.mm"
include "pm2.61i.mm"

theorem eueq2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume eueq2.1: |- A e. _V
  assume eueq2.2: |- B e. _V

  disjoint ph x
  disjoint A x
  disjoint B x
  assert |- E! x ( ( ph /\ x = A ) \/ ( -. ph /\ x = B ) )

  proof
    wph
    wph
    vx
    cv
    #
    cA
    wceq
    #
    wa
    #
    wph
    wn
    #
    @0
    cB
    wceq
    #
    wa
    #
    wo
    #
    vx
    weu
    #
    wph
    @3
    @2
    wo
    #
    vx
    weu
    #
    @7
    wph
    @3
    wn
    @2
    vx
    weu
    #
    @9
    wph
    notnot
    #
    wph
    @1
    vx
    weu
    #
    @10
    vx
    cA
    eueq2.1
    eueq1
    @10
    wph
    @12
    wa
    wph
    @1
    vx
    euanv
    biimpri
    mpan2
    @3
    @2
    vx
    euorv
    syl2anc
    wph
    @8
    @6
    vx
    @8
    @2
    @3
    wo
    wph
    @6
    @3
    @2
    orcom
    wph
    @3
    @5
    @2
    wph
    @3
    @4
    @11
    bianfd
    orbi2d
    syl5bb
    eubidv
    mpbid
    @3
    wph
    @5
    wo
    #
    vx
    weu
    #
    @7
    @3
    @5
    vx
    weu
    #
    @14
    @3
    @4
    vx
    weu
    #
    @15
    vx
    cB
    eueq2.2
    eueq1
    @15
    @3
    @16
    wa
    @3
    @4
    vx
    euanv
    biimpri
    mpan2
    wph
    @5
    vx
    euorv
    mpdan
    @3
    @13
    @6
    vx
    @3
    wph
    @2
    @5
    @3
    wph
    @1
    @3
    id
    bianfd
    orbi1d
    eubidv
    mpbid
    pm2.61i
end
