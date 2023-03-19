include "cv.mm"
include "cin.mm"
include "wcel.mm"
include "weu.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "ineq2.mm"
include "eleq2d.mm"
include "eubidv.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "cbvexv.mm"
include "cuni.mm"
include "csn.mm"
include "cun.mm"
include "indi.mm"
include "c0.mm"
include "elssuni.mm"
include "ssneld.mm"
include "disjsn.mm"
include "syl6ibr.mm"
include "impcom.mm"
include "uneq2d.mm"
include "un0.mm"
include "syl6eq.mm"
include "syl5req.mm"
include "ralbidva.mm"
include "wo.mm"
include "vsnid.mm"
include "olci.mm"
include "elun.mm"
include "mpbir.mm"
include "sseld.mm"
include "mpi.mm"
include "con3i.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "eleq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl6bi.mm"
include "vuniex.mm"
include "eleq2.mm"
include "exbidv.mm"
include "wal.mm"
include "nalset.mm"
include "alexn.mm"
include "spi.mm"
include "vtocl.mm"
include "exlimiiv.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "exsimpr.mm"
include "impbii.mm"

theorem kmlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vv: setvar v
  let vu: setvar u
  let wps: wff ps

  disjoint x y
  disjoint ph x
  disjoint ph y
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
  disjoint ps x
  disjoint ps v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  assert |- ( E. y A. z e. x ( ph -> E! w w e. ( z i^i y ) ) <-> E. y ( -. y e. x /\ A. z e. x ( ph -> E! w w e. ( z i^i y ) ) ) )

  proof
    wph
    vw
    cv
    #
    vz
    cv
    #
    vy
    cv
    #
    cin
    #
    wcel
    #
    vw
    weu
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
    @2
    @7
    wcel
    #
    wn
    #
    @8
    wa
    #
    vy
    wex
    #
    @9
    wph
    @0
    @1
    vv
    cv
    #
    cin
    #
    wcel
    #
    vw
    weu
    #
    wi
    #
    vz
    @7
    wral
    #
    vv
    wex
    @13
    @8
    @19
    vy
    vv
    @2
    @14
    wceq
    #
    @6
    @18
    vz
    @7
    @20
    @5
    @17
    wph
    @20
    @4
    @16
    vw
    @20
    @3
    @15
    @0
    @2
    @14
    @1
    ineq2
    eleq2d
    eubidv
    imbi2d
    ralbidv
    cbvexv
    @19
    @13
    vv
    vu
    cv
    #
    @7
    cuni
    #
    wcel
    #
    wn
    #
    @19
    @13
    wi
    vu
    @24
    @19
    @14
    @21
    csn
    #
    cun
    #
    @7
    wcel
    #
    wn
    #
    wph
    @0
    @1
    @26
    cin
    #
    wcel
    #
    vw
    weu
    #
    wi
    #
    vz
    @7
    wral
    #
    wa
    #
    @13
    @24
    @19
    @33
    @34
    @24
    @18
    @32
    vz
    @7
    @24
    @1
    @7
    wcel
    #
    wa
    #
    @17
    @31
    wph
    @36
    @16
    @30
    vw
    @36
    @15
    @29
    @0
    @36
    @29
    @15
    @1
    @25
    cin
    #
    cun
    #
    @15
    @1
    @14
    @25
    indi
    @36
    @38
    @15
    c0
    cun
    @15
    @36
    @37
    c0
    @15
    @35
    @24
    @37
    c0
    wceq
    #
    @35
    @24
    @21
    @1
    wcel
    wn
    @39
    @35
    @1
    @22
    @21
    @1
    @7
    elssuni
    ssneld
    @1
    @21
    disjsn
    syl6ibr
    impcom
    uneq2d
    @15
    un0
    syl6eq
    syl5req
    eleq2d
    eubidv
    imbi2d
    ralbidva
    @24
    @28
    @33
    @27
    @23
    @27
    @21
    @26
    wcel
    #
    @23
    @40
    @21
    @14
    wcel
    #
    @21
    @25
    wcel
    #
    wo
    @42
    @41
    vu
    vsnid
    olci
    @21
    @14
    @25
    elun
    mpbir
    @27
    @26
    @22
    @21
    @26
    @7
    elssuni
    sseld
    mpi
    con3i
    biantrurd
    bitrd
    @12
    @34
    vy
    @26
    @14
    @25
    vv
    vex
    @21
    snex
    unex
    @2
    @26
    wceq
    #
    @11
    @28
    @8
    @33
    @43
    @10
    @27
    @2
    @26
    @7
    eleq1
    notbid
    @43
    @6
    @32
    vz
    @7
    @43
    @5
    @31
    wph
    @43
    @4
    @30
    vw
    @43
    @3
    @29
    @0
    @2
    @26
    @1
    ineq2
    eleq2d
    eubidv
    imbi2d
    ralbidv
    anbi12d
    spcev
    syl6bi
    @21
    @2
    wcel
    #
    wn
    #
    vu
    wex
    #
    @24
    vu
    wex
    vy
    @22
    vx
    vuniex
    @2
    @22
    wceq
    #
    @45
    @24
    vu
    @47
    @44
    @23
    @2
    @22
    @21
    eleq2
    notbid
    exbidv
    @46
    vy
    @46
    vy
    wal
    @44
    vu
    wal
    vy
    wex
    wn
    vy
    vu
    nalset
    @44
    vy
    vu
    alexn
    mpbir
    spi
    vtocl
    exlimiiv
    exlimiv
    sylbi
    @11
    @8
    vy
    exsimpr
    impbii
end
