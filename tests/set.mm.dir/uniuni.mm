include "wel.mm"
include "cv.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "wceq.mm"
include "eluni.mm"
include "anbi2i.mm"
include "exbii.mm"
include "19.42v.mm"
include "bicomi.mm"
include "excom.mm"
include "anass.mm"
include "ancom.mm"
include "bitr3i.mm"
include "2exbii.mm"
include "exdistr.mm"
include "3bitri.mm"
include "vuniex.mm"
include "eleq2.mm"
include "ceqsexv.mm"
include "exancom.mm"
include "bitri.mm"
include "3bitr2i.mm"
include "vex.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "elab.mm"
include "abbii.mm"
include "df-uni.mm"
include "3eqtr4i.mm"

theorem uniuni
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vv: setvar v
  let vz: setvar z
  let vu: setvar u

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A v
  disjoint A z
  disjoint v x
  disjoint x z
  disjoint v y
  disjoint y z
  disjoint v z
  disjoint A u
  disjoint u x
  disjoint u y
  disjoint u z
  assert |- U. U. A = U. { x | E. y ( x = U. y /\ y e. A ) }

  proof
    vz
    vu
    wel
    #
    vu
    cv
    #
    cA
    cuni
    #
    wcel
    #
    wa
    #
    vu
    wex
    #
    vz
    cab
    vz
    vv
    wel
    #
    vv
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cuni
    #
    wceq
    #
    @9
    cA
    wcel
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    wcel
    #
    wa
    #
    vv
    wex
    #
    vz
    cab
    @2
    cuni
    @15
    cuni
    @5
    @18
    vz
    @5
    @0
    vu
    vy
    wel
    #
    @12
    wa
    #
    vy
    wex
    #
    wa
    #
    vu
    wex
    #
    @12
    vz
    cv
    #
    @10
    wcel
    #
    wa
    #
    vy
    wex
    #
    @18
    @4
    @22
    vu
    @3
    @21
    @0
    vy
    @1
    cA
    eluni
    anbi2i
    exbii
    @23
    @0
    @20
    wa
    #
    vy
    wex
    #
    vu
    wex
    #
    @12
    @0
    @19
    wa
    #
    vu
    wex
    #
    wa
    #
    vy
    wex
    #
    @27
    @22
    @29
    vu
    @29
    @22
    @0
    @20
    vy
    19.42v
    bicomi
    exbii
    @30
    @28
    vu
    wex
    vy
    wex
    @12
    @31
    wa
    #
    vu
    wex
    vy
    wex
    @34
    @28
    vu
    vy
    excom
    @28
    @35
    vy
    vu
    @28
    @31
    @12
    wa
    @35
    @0
    @19
    @12
    anass
    @31
    @12
    ancom
    bitr3i
    2exbii
    @12
    @31
    vy
    vu
    exdistr
    3bitri
    @33
    @26
    vy
    @32
    @25
    @12
    @25
    @32
    vu
    @24
    @9
    eluni
    bicomi
    anbi2i
    exbii
    3bitri
    @27
    @6
    @7
    @10
    wceq
    #
    @12
    wa
    #
    wa
    #
    vv
    wex
    #
    vy
    wex
    @38
    vy
    wex
    vv
    wex
    #
    @18
    @26
    @39
    vy
    @26
    @12
    @6
    @36
    wa
    #
    vv
    wex
    #
    wa
    @12
    @41
    wa
    #
    vv
    wex
    @39
    @25
    @42
    @12
    @25
    @36
    @6
    wa
    vv
    wex
    @42
    @6
    @25
    vv
    @10
    vy
    vuniex
    @7
    @10
    @24
    eleq2
    ceqsexv
    @36
    @6
    vv
    exancom
    bitr3i
    anbi2i
    @12
    @41
    vv
    19.42v
    @43
    @38
    vv
    @43
    @41
    @12
    wa
    @38
    @12
    @41
    ancom
    @6
    @36
    @12
    anass
    bitri
    exbii
    3bitr2i
    exbii
    @38
    vy
    vv
    excom
    @40
    @6
    @37
    vy
    wex
    #
    wa
    #
    vv
    wex
    @18
    @6
    @37
    vv
    vy
    exdistr
    @45
    @17
    vv
    @44
    @16
    @6
    @16
    @44
    @14
    @44
    vx
    @7
    vv
    vex
    @8
    @7
    wceq
    #
    @13
    @37
    vy
    @46
    @11
    @36
    @12
    @8
    @7
    @10
    eqeq1
    anbi1d
    exbidv
    elab
    bicomi
    anbi2i
    exbii
    bitri
    3bitri
    3bitri
    abbii
    vz
    vu
    @2
    df-uni
    vz
    vv
    @15
    df-uni
    3eqtr4i
end
