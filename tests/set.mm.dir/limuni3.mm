include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wlim.mm"
include "wral.mm"
include "wa.mm"
include "cuni.mm"
include "word.mm"
include "wcel.mm"
include "csuc.mm"
include "con0.mm"
include "wss.mm"
include "limeq.mm"
include "rspcv.mm"
include "cvv.mm"
include "vex.mm"
include "limelon.mm"
include "mpan.mm"
include "syl6com.mm"
include "ssrdv.mm"
include "ssorduni.mm"
include "syl.mm"
include "adantl.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "0ellim.mm"
include "elunii.mm"
include "expcom.mm"
include "syl5.mm"
include "syld.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "imp.mm"
include "wrex.mm"
include "eluni2.mm"
include "rspccv.mm"
include "limsuc.mm"
include "anbi1d.mm"
include "syl6bi.mm"
include "expd.mm"
include "com3r.mm"
include "sylcom.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "dflim4.mm"
include "syl3anbrc.mm"

theorem limuni3
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( ( A =/= (/) /\ A. x e. A Lim x ) -> Lim U. A )

  proof
    cA
    c0
    wne
    #
    vx
    cv
    #
    wlim
    #
    vx
    cA
    wral
    #
    wa
    cA
    cuni
    #
    word
    #
    c0
    @4
    wcel
    #
    vy
    cv
    #
    csuc
    #
    @4
    wcel
    #
    vy
    @4
    wral
    #
    @4
    wlim
    @3
    @5
    @0
    @3
    cA
    con0
    wss
    @5
    @3
    vz
    cA
    con0
    vz
    cv
    #
    cA
    wcel
    #
    @3
    @11
    wlim
    #
    @11
    con0
    wcel
    #
    @2
    @13
    vx
    @11
    cA
    @1
    @11
    limeq
    #
    rspcv
    #
    @11
    cvv
    wcel
    @13
    @14
    vz
    vex
    @11
    cvv
    limelon
    mpan
    syl6com
    ssrdv
    cA
    ssorduni
    syl
    adantl
    @0
    @3
    @6
    @0
    @12
    vz
    wex
    @3
    @6
    wi
    #
    vz
    cA
    n0
    @12
    @17
    vz
    @12
    @3
    @13
    @6
    @16
    @13
    c0
    @11
    wcel
    #
    @12
    @6
    @11
    0ellim
    @18
    @12
    @6
    c0
    @11
    cA
    elunii
    expcom
    syl5
    syld
    exlimiv
    sylbi
    imp
    @3
    @10
    @0
    @3
    @9
    vy
    @4
    @7
    @4
    wcel
    @7
    @11
    wcel
    #
    vz
    cA
    wrex
    @3
    @9
    vz
    @7
    cA
    eluni2
    @3
    @19
    @9
    vz
    cA
    @3
    @12
    @13
    @19
    @9
    wi
    @2
    @13
    vx
    @11
    cA
    @15
    rspccv
    @13
    @19
    @12
    @9
    @13
    @19
    @12
    @9
    @13
    @19
    @12
    wa
    @8
    @11
    wcel
    #
    @12
    wa
    @9
    @13
    @19
    @20
    @12
    @11
    @7
    limsuc
    anbi1d
    @8
    @11
    cA
    elunii
    syl6bi
    expd
    com3r
    sylcom
    rexlimdv
    syl5bi
    ralrimiv
    adantl
    vy
    @4
    dflim4
    syl3anbrc
end
