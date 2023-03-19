include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wel.mm"
include "wa.mm"
include "wrex.mm"
include "wreu.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wal.mm"
include "cfv.mm"
include "wcel.mm"
include "wac.mm"
include "crab.mm"
include "cuni.mm"
include "cmpt.mm"
include "crio.mm"
include "riotauni.mm"
include "riotacl.mm"
include "eqeltrrd.mm"
include "wceq.mm"
include "elequ2.mm"
include "elequ1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "rabbidva2.mm"
include "unieqd.mm"
include "eqid.mm"
include "vex.mm"
include "rabex.mm"
include "uniex.mm"
include "fvmpt.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "imim2d.mm"
include "ralimia.mm"
include "cpw.mm"
include "wf.mm"
include "cvv.mm"
include "wss.mm"
include "ssrab2.mm"
include "elssuni.mm"
include "syl5ss.mm"
include "unissd.mm"
include "elpw2.mm"
include "sylibr.mm"
include "fmpti.mm"
include "pwex.mm"
include "fex2.mm"
include "mp3an.mm"
include "fveq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "spcev.mm"
include "syl.mm"
include "exlimiv.mm"
include "alimi.mm"
include "dfac3.mm"

theorem dfac2a
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  let vu: setvar u

  disjoint x z
  disjoint x y
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w z
  disjoint v z
  disjoint w y
  disjoint v y
  disjoint v w
  disjoint f x
  disjoint u x
  disjoint f z
  disjoint u z
  disjoint f y
  disjoint f w
  disjoint f v
  disjoint f u
  disjoint u y
  disjoint u w
  disjoint u v
  assert |- ( A. x E. y A. z e. x ( z =/= (/) -> E! w e. z E. v e. y ( z e. v /\ w e. v ) ) -> CHOICE )

  proof
    vz
    cv
    #
    c0
    wne
    #
    vz
    vv
    wel
    #
    vw
    vv
    wel
    #
    wa
    #
    vv
    vy
    cv
    #
    wrex
    #
    vw
    @0
    wreu
    #
    wi
    #
    vz
    vx
    cv
    #
    wral
    #
    vy
    wex
    #
    vx
    wal
    @1
    @0
    vf
    cv
    #
    cfv
    #
    @0
    wcel
    #
    wi
    #
    vz
    @9
    wral
    #
    vf
    wex
    #
    vx
    wal
    wac
    @11
    @17
    vx
    @10
    @17
    vy
    @10
    @1
    @0
    vu
    @9
    vu
    vv
    wel
    #
    @3
    wa
    #
    vv
    @5
    wrex
    #
    vw
    vu
    cv
    #
    crab
    #
    cuni
    #
    cmpt
    #
    cfv
    #
    @0
    wcel
    #
    wi
    #
    vz
    @9
    wral
    #
    @17
    @8
    @27
    vz
    @9
    vz
    vx
    wel
    #
    @7
    @26
    @1
    @7
    @26
    @29
    @6
    vw
    @0
    crab
    #
    cuni
    #
    @0
    wcel
    @7
    @6
    vw
    @0
    crio
    @31
    @0
    @6
    vw
    @0
    riotauni
    @6
    vw
    @0
    riotacl
    eqeltrrd
    @29
    @25
    @31
    @0
    vu
    @0
    @23
    @31
    @9
    @24
    @21
    @0
    wceq
    #
    @22
    @30
    @32
    @20
    @6
    vw
    @21
    @0
    @32
    vw
    vu
    wel
    vw
    vz
    wel
    @20
    @6
    vu
    vz
    vw
    elequ2
    @32
    @19
    @4
    vv
    @5
    @32
    @18
    @2
    @3
    vu
    vz
    vv
    elequ1
    anbi1d
    rexbidv
    anbi12d
    rabbidva2
    unieqd
    @24
    eqid
    #
    @30
    @6
    vw
    @0
    vz
    vex
    rabex
    uniex
    fvmpt
    eleq1d
    syl5ibr
    imim2d
    ralimia
    @16
    @28
    vf
    @24
    @9
    @9
    cuni
    #
    cuni
    #
    cpw
    #
    @24
    wf
    @9
    cvv
    wcel
    @36
    cvv
    wcel
    @24
    cvv
    wcel
    vu
    @9
    @36
    @23
    @24
    @33
    vu
    vx
    wel
    #
    @23
    @35
    wss
    @23
    @36
    wcel
    @37
    @22
    @34
    @37
    @22
    @21
    @34
    @20
    vw
    @21
    ssrab2
    @21
    @9
    elssuni
    syl5ss
    unissd
    @23
    @35
    @34
    @9
    vx
    vex
    #
    uniex
    uniex
    #
    elpw2
    sylibr
    fmpti
    @38
    @35
    @39
    pwex
    @9
    @36
    @24
    cvv
    cvv
    fex2
    mp3an
    @12
    @24
    wceq
    #
    @15
    @27
    vz
    @9
    @40
    @14
    @26
    @1
    @40
    @13
    @25
    @0
    @0
    @12
    @24
    fveq1
    eleq1d
    imbi2d
    ralbidv
    spcev
    syl
    exlimiv
    alimi
    vx
    vz
    vf
    dfac3
    sylibr
end
