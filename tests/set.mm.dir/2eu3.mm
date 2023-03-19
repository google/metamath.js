include "wmo.mm"
include "wo.mm"
include "wal.mm"
include "weu.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "nfmo1.mm"
include "19.31.mm"
include "albii.mm"
include "nfal.mm"
include "19.32.mm"
include "bitri.mm"
include "wi.mm"
include "2eu1.mm"
include "biimpd.mm"
include "ancom.mm"
include "syl6ib.mm"
include "adantld.mm"
include "adantrd.mm"
include "jaoi.mm"
include "2exeu.mm"
include "ancoms.mm"
include "jca.mm"
include "impbid1.mm"
include "sylbi.mm"

theorem 2eu3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( E* x ph \/ E* y ph ) -> ( ( E! x E! y ph /\ E! y E! x ph ) <-> ( E! x E. y ph /\ E! y E. x ph ) ) )

  proof
    wph
    vx
    wmo
    #
    wph
    vy
    wmo
    #
    wo
    vy
    wal
    #
    vx
    wal
    #
    @0
    vy
    wal
    #
    @1
    vx
    wal
    #
    wo
    #
    wph
    vy
    weu
    vx
    weu
    #
    wph
    vx
    weu
    vy
    weu
    #
    wa
    #
    wph
    vy
    wex
    vx
    weu
    #
    wph
    vx
    wex
    vy
    weu
    #
    wa
    #
    wb
    @3
    @4
    @1
    wo
    #
    vx
    wal
    @6
    @2
    @13
    vx
    @0
    @1
    vy
    wph
    vy
    nfmo1
    19.31
    albii
    @4
    @1
    vx
    @0
    vx
    vy
    wph
    vx
    nfmo1
    nfal
    19.32
    bitri
    @6
    @9
    @12
    @4
    @9
    @12
    wi
    @5
    @4
    @8
    @12
    @7
    @4
    @8
    @11
    @10
    wa
    #
    @12
    @4
    @8
    @14
    wph
    vy
    vx
    2eu1
    biimpd
    @11
    @10
    ancom
    syl6ib
    adantld
    @5
    @7
    @12
    @8
    @5
    @7
    @12
    wph
    vx
    vy
    2eu1
    biimpd
    adantrd
    jaoi
    @12
    @7
    @8
    wph
    vx
    vy
    2exeu
    @11
    @10
    @8
    wph
    vy
    vx
    2exeu
    ancoms
    jca
    impbid1
    sylbi
end
