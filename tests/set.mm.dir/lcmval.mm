include "cz.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "clcm.mm"
include "eqeq1.mm"
include "orbi1d.mm"
include "breq1.mm"
include "anbi1d.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "ifbieq2d.mm"
include "orbi2d.mm"
include "anbi2d.mm"
include "df-lcm.mm"
include "c0ex.mm"
include "ltso.mm"
include "infex.mm"
include "ifex.mm"
include "ovmpt2.mm"

theorem lcmval
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y

  disjoint M n
  disjoint N n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M lcm N ) = if ( ( M = 0 \/ N = 0 ) , 0 , inf ( { n e. NN | ( M || n /\ N || n ) } , RR , < ) ) )

  proof
    vx
    vy
    cM
    cN
    cz
    cz
    vx
    cv
    #
    cc0
    wceq
    #
    vy
    cv
    #
    cc0
    wceq
    #
    wo
    #
    cc0
    @0
    vn
    cv
    #
    cdvds
    wbr
    #
    @2
    @5
    cdvds
    wbr
    #
    wa
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cif
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wo
    #
    cc0
    cM
    @5
    cdvds
    wbr
    #
    cN
    @5
    cdvds
    wbr
    #
    wa
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cif
    clcm
    @11
    @3
    wo
    #
    cc0
    @14
    @7
    wa
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cif
    @0
    cM
    wceq
    #
    @4
    @19
    @10
    @22
    cc0
    @23
    @1
    @11
    @3
    @0
    cM
    cc0
    eqeq1
    orbi1d
    @23
    cr
    @9
    @21
    clt
    @23
    @8
    @20
    vn
    cn
    @23
    @6
    @14
    @7
    @0
    cM
    @5
    cdvds
    breq1
    anbi1d
    rabbidv
    infeq1d
    ifbieq2d
    @2
    cN
    wceq
    #
    @19
    @13
    @22
    @18
    cc0
    @24
    @3
    @12
    @11
    @2
    cN
    cc0
    eqeq1
    orbi2d
    @24
    cr
    @21
    @17
    clt
    @24
    @20
    @16
    vn
    cn
    @24
    @7
    @15
    @14
    @2
    cN
    @5
    cdvds
    breq1
    anbi2d
    rabbidv
    infeq1d
    ifbieq2d
    vx
    vy
    vn
    df-lcm
    @13
    cc0
    @18
    c0ex
    cr
    @17
    clt
    ltso
    infex
    ifex
    ovmpt2
end
