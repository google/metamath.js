include "cv.mm"
include "cpw.mm"
include "cvv.mm"
include "wcel.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "w3a.mm"
include "simpl.mm"
include "ralimi.mm"
include "wceq.mm"
include "pweq.mm"
include "sseq1d.mm"
include "rspccv.mm"
include "syl.mm"
include "anim2i.mm"
include "3adant3.mm"
include "pm3.35.mm"
include "vex.mm"
include "ssex.mm"
include "3syl.mm"
include "axgroth5.mm"
include "exlimiiv.mm"
include "pwidg.mm"
include "eleq2d.mm"
include "spcegv.mm"
include "mpd.mm"
include "elex.mm"
include "exlimiv.mm"
include "impbii.mm"
include "elpw2.mm"
include "pwss.mm"
include "dfss2.mm"
include "imbi1i.mm"
include "albii.mm"
include "bitri.mm"
include "exbii.mm"
include "mpbi.mm"

theorem grothpw
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint v x
  disjoint u x
  disjoint v y
  disjoint u y
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint u v
  assert |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y )

  proof
    vx
    cv
    #
    cpw
    #
    cvv
    wcel
    #
    vw
    vz
    wel
    vw
    vx
    wel
    wi
    vw
    wal
    #
    vz
    vy
    wel
    #
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    vx
    vy
    wel
    #
    vz
    cv
    #
    cpw
    #
    vy
    cv
    #
    wss
    #
    @10
    vw
    cv
    wss
    vw
    @11
    wrex
    #
    wa
    #
    vz
    @11
    wral
    #
    @9
    @11
    cen
    wbr
    @4
    wo
    vz
    @11
    cpw
    #
    wral
    #
    w3a
    #
    @2
    vy
    @18
    @8
    @8
    @1
    @11
    wss
    #
    wi
    #
    wa
    #
    @19
    @2
    @8
    @15
    @21
    @17
    @15
    @20
    @8
    @15
    @12
    vz
    @11
    wral
    @20
    @14
    @12
    vz
    @11
    @12
    @13
    simpl
    ralimi
    @12
    @19
    vz
    @0
    @11
    @9
    @0
    wceq
    @10
    @1
    @11
    @9
    @0
    pweq
    sseq1d
    rspccv
    syl
    anim2i
    3adant3
    @8
    @19
    pm3.35
    @1
    @11
    vy
    vex
    #
    ssex
    3syl
    vx
    vy
    vz
    vw
    axgroth5
    exlimiiv
    @2
    @1
    @16
    wcel
    #
    vy
    wex
    #
    @7
    @2
    @24
    @2
    @1
    @1
    cpw
    #
    wcel
    #
    @24
    @1
    cvv
    pwidg
    @23
    @26
    vy
    @1
    cvv
    @11
    @1
    wceq
    @16
    @25
    @1
    @11
    @1
    pweq
    eleq2d
    spcegv
    mpd
    @23
    @2
    vy
    @1
    @16
    elex
    exlimiv
    impbii
    @23
    @6
    vy
    @23
    @19
    @6
    @1
    @11
    @22
    elpw2
    @19
    @9
    @0
    wss
    #
    @4
    wi
    #
    vz
    wal
    @6
    vz
    @0
    @11
    pwss
    @28
    @5
    vz
    @27
    @3
    @4
    vw
    @9
    @0
    dfss2
    imbi1i
    albii
    bitri
    bitri
    exbii
    bitri
    mpbi
end
