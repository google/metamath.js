include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "cgcd.mm"
include "co.mm"
include "ancom.mm"
include "rabbii.mm"
include "supeq1i.mm"
include "ifbieq2i.mm"
include "gcdval.mm"
include "ancoms.mm"
include "3eqtr4a.mm"

theorem gcdcom
  let cM: class M
  let cN: class N
  let vn: setvar n


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M gcd N ) = ( N gcd M ) )

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
    wa
    #
    cc0
    vn
    cv
    #
    cM
    cdvds
    wbr
    #
    @5
    cN
    cdvds
    wbr
    #
    wa
    #
    vn
    cz
    crab
    #
    cr
    clt
    csup
    #
    cif
    @3
    @2
    wa
    #
    cc0
    @7
    @6
    wa
    #
    vn
    cz
    crab
    #
    cr
    clt
    csup
    #
    cif
    #
    cM
    cN
    cgcd
    co
    cN
    cM
    cgcd
    co
    #
    @4
    @11
    @10
    @14
    cc0
    @2
    @3
    ancom
    cr
    @9
    @13
    clt
    @8
    @12
    vn
    cz
    @6
    @7
    ancom
    rabbii
    supeq1i
    ifbieq2i
    vn
    cM
    cN
    gcdval
    @1
    @0
    @16
    @15
    wceq
    vn
    cN
    cM
    gcdval
    ancoms
    3eqtr4a
end
