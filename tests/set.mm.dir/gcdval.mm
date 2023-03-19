include "cz.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "cgcd.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "breq2.mm"
include "rabbidv.mm"
include "supeq1d.mm"
include "ifbieq2d.mm"
include "anbi2d.mm"
include "df-gcd.mm"
include "c0ex.mm"
include "ltso.mm"
include "supex.mm"
include "ifex.mm"
include "ovmpt2.mm"

theorem gcdval
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y

  disjoint M n
  disjoint N n
  disjoint M x
  disjoint M y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M gcd N ) = if ( ( M = 0 /\ N = 0 ) , 0 , sup ( { n e. ZZ | ( n || M /\ n || N ) } , RR , < ) ) )

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
    wa
    #
    cc0
    vn
    cv
    #
    @0
    cdvds
    wbr
    #
    @5
    @2
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
    @5
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
    cgcd
    @11
    @3
    wa
    #
    cc0
    @14
    @7
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
    anbi1d
    @23
    cr
    @9
    @21
    clt
    @23
    @8
    @20
    vn
    cz
    @23
    @6
    @14
    @7
    @0
    cM
    @5
    cdvds
    breq2
    anbi1d
    rabbidv
    supeq1d
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
    anbi2d
    @24
    cr
    @21
    @17
    clt
    @24
    @20
    @16
    vn
    cz
    @24
    @7
    @15
    @14
    @2
    cN
    @5
    cdvds
    breq2
    anbi2d
    rabbidv
    supeq1d
    ifbieq2d
    vx
    vy
    vn
    df-gcd
    @13
    cc0
    @18
    c0ex
    cr
    @17
    clt
    ltso
    supex
    ifex
    ovmpt2
end
