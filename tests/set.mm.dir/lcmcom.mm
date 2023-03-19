include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "clcm.mm"
include "co.mm"
include "orcom.mm"
include "ancom.mm"
include "rabbii.mm"
include "infeq1i.mm"
include "ifbieq2i.mm"
include "lcmval.mm"
include "ancoms.mm"
include "3eqtr4a.mm"

theorem lcmcom
  let cM: class M
  let cN: class N
  let cK: class K
  let vn: setvar n


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M lcm N ) = ( N lcm M ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
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
    vn
    cv
    #
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
    @3
    @2
    wo
    #
    cc0
    @7
    @6
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
    #
    cM
    cN
    clcm
    co
    cN
    cM
    clcm
    co
    #
    @4
    @11
    @10
    @14
    cc0
    @2
    @3
    orcom
    cr
    @9
    @13
    clt
    @8
    @12
    vn
    cn
    @6
    @7
    ancom
    rabbii
    infeq1i
    ifbieq2i
    vn
    cM
    cN
    lcmval
    @1
    @0
    @16
    @15
    wceq
    vn
    cN
    cM
    lcmval
    ancoms
    3eqtr4a
end
