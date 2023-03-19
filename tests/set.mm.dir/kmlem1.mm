include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "crab.mm"
include "vex.mm"
include "rabex.mm"
include "wceq.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "spcv.mm"
include "alrimiv.mm"
include "wcel.mm"
include "elrabi.mm"
include "imim1i.mm"
include "ralimi2.mm"
include "imim12i.mm"
include "neeq1.mm"
include "elrab.mm"
include "simprbi.mm"
include "rgen.mm"
include "jctil.mm"
include "biimpri.mm"
include "expd.mm"
include "eximi.mm"
include "sylg.mm"
include "cbvalv.mm"
include "sylib.mm"

theorem kmlem1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint A v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint ps v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  assert |- ( A. x ( ( A. z e. x z =/= (/) /\ A. z e. x A. w e. x ph ) -> E. y A. z e. x ps ) -> A. x ( A. z e. x A. w e. x ph -> E. y A. z e. x ( z =/= (/) -> ps ) ) )

  proof
    vz
    cv
    #
    c0
    wne
    #
    vz
    vx
    cv
    #
    wral
    #
    wph
    vw
    @2
    wral
    #
    vz
    @2
    wral
    #
    wa
    #
    wps
    vz
    @2
    wral
    #
    vy
    wex
    #
    wi
    #
    vx
    wal
    #
    wph
    vw
    vv
    cv
    #
    wral
    #
    vz
    @11
    wral
    #
    @1
    wps
    wi
    #
    vz
    @11
    wral
    #
    vy
    wex
    #
    wi
    #
    vv
    wal
    @5
    @14
    vz
    @2
    wral
    #
    vy
    wex
    #
    wi
    #
    vx
    wal
    @10
    @1
    vz
    vu
    cv
    #
    c0
    wne
    #
    vu
    @11
    crab
    #
    wral
    #
    wph
    vw
    @23
    wral
    #
    vz
    @23
    wral
    #
    wa
    #
    wps
    vz
    @23
    wral
    #
    vy
    wex
    #
    wi
    #
    @17
    vv
    @10
    @30
    vv
    @9
    @30
    vx
    @23
    @22
    vu
    @11
    vv
    vex
    rabex
    @2
    @23
    wceq
    #
    @6
    @27
    @8
    @29
    @31
    @3
    @24
    @5
    @26
    @1
    vz
    @2
    @23
    raleq
    @4
    @25
    vz
    @2
    @23
    wph
    vw
    @2
    @23
    raleq
    raleqbi1dv
    anbi12d
    @31
    @7
    @28
    vy
    wps
    vz
    @2
    @23
    raleq
    exbidv
    imbi12d
    spcv
    alrimiv
    @13
    @27
    @29
    @16
    @13
    @26
    @24
    @12
    @25
    vz
    @11
    @23
    @0
    @23
    wcel
    #
    @0
    @11
    wcel
    #
    @12
    @25
    @22
    vu
    @0
    @11
    elrabi
    wph
    wph
    vw
    @11
    @23
    vw
    cv
    #
    @23
    wcel
    @34
    @11
    wcel
    wph
    @22
    vu
    @34
    @11
    elrabi
    imim1i
    ralimi2
    imim12i
    ralimi2
    @1
    vz
    @23
    @32
    @33
    @1
    @22
    @1
    vu
    @0
    @11
    @21
    @0
    c0
    neeq1
    elrab
    #
    simprbi
    rgen
    jctil
    @28
    @15
    vy
    wps
    @14
    vz
    @23
    @11
    @32
    wps
    wi
    @33
    @1
    wps
    @33
    @1
    wa
    #
    @32
    wps
    @32
    @36
    @35
    biimpri
    imim1i
    expd
    ralimi2
    eximi
    imim12i
    sylg
    @17
    @20
    vv
    vx
    @11
    @2
    wceq
    #
    @13
    @5
    @16
    @19
    @12
    @4
    vz
    @11
    @2
    wph
    vw
    @11
    @2
    raleq
    raleqbi1dv
    @37
    @15
    @18
    vy
    @14
    vz
    @11
    @2
    raleq
    exbidv
    imbi12d
    cbvalv
    sylib
end
