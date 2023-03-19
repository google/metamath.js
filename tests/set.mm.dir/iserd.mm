include "cdm.mm"
include "wer.mm"
include "wrel.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "wal.mm"
include "eqidd.mm"
include "ex.mm"
include "jca.mm"
include "alrimiv.mm"
include "dfer2.mm"
include "syl3anbrc.mm"
include "wb.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "erref.mm"
include "vex.mm"
include "breldm.mm"
include "impbid1.mm"
include "bitr4d.mm"
include "eqrdv.mm"
include "ereq2.mm"
include "syl.mm"
include "mpbid.mm"

theorem iserd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume iserd.1: |- ( ph -> Rel R )
  assume iserd.2: |- ( ( ph /\ x R y ) -> y R x )
  assume iserd.3: |- ( ( ph /\ ( x R y /\ y R z ) ) -> x R z )
  assume iserd.4: |- ( ph -> ( x e. A <-> x R x ) )

  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint A x
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> R Er A )

  proof
    wph
    cR
    cdm
    #
    cR
    wer
    #
    cA
    cR
    wer
    #
    wph
    cR
    wrel
    @0
    @0
    wceq
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @4
    @3
    cR
    wbr
    #
    wi
    #
    @5
    @4
    vz
    cv
    #
    cR
    wbr
    wa
    #
    @3
    @8
    cR
    wbr
    #
    wi
    #
    wa
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    @1
    iserd.1
    wph
    @0
    eqidd
    wph
    @14
    vx
    wph
    @13
    vy
    wph
    @12
    vz
    wph
    @7
    @11
    wph
    @5
    @6
    iserd.2
    ex
    wph
    @9
    @10
    iserd.3
    ex
    jca
    alrimiv
    alrimiv
    alrimiv
    vx
    vy
    vz
    @0
    cR
    dfer2
    syl3anbrc
    #
    wph
    @0
    cA
    wceq
    @1
    @2
    wb
    wph
    vx
    @0
    cA
    wph
    @3
    @0
    wcel
    #
    @3
    @3
    cR
    wbr
    #
    @3
    cA
    wcel
    wph
    @16
    @17
    wph
    @16
    @17
    wph
    @16
    wa
    @3
    cR
    @0
    wph
    @1
    @16
    @15
    adantr
    wph
    @16
    simpr
    erref
    ex
    @3
    @3
    cR
    vx
    vex
    #
    @18
    breldm
    impbid1
    iserd.4
    bitr4d
    eqrdv
    @0
    cA
    cR
    ereq2
    syl
    mpbid
end
