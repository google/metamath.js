include "cprime.mm"
include "wcel.mm"
include "c4.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cgz.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cmpt.mm"
include "crn.mm"
include "caddc.mm"
include "cz.mm"
include "wrex.mm"
include "cgcd.mm"
include "cab.mm"
include "eqid.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cbvrex2v.mm"
include "abbii.mm"
include "2sqlem11.mm"
include "2sqlem2.mm"
include "sylib.mm"

theorem 2sq
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint P x
  disjoint P y
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint P a
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint P b
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint P w
  disjoint x z
  disjoint y z
  disjoint P z
  assert |- ( ( P e. Prime /\ ( P mod 4 ) = 1 ) -> E. x e. ZZ E. y e. ZZ P = ( ( x ^ 2 ) + ( y ^ 2 ) ) )

  proof
    cP
    cprime
    wcel
    cP
    c4
    cmo
    co
    c1
    wceq
    wa
    cP
    vw
    cgz
    vw
    cv
    cabs
    cfv
    c2
    cexp
    co
    cmpt
    crn
    #
    wcel
    cP
    vx
    cv
    #
    c2
    cexp
    co
    #
    vy
    cv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    vy
    cz
    wrex
    vx
    cz
    wrex
    vx
    vy
    vz
    vw
    cP
    @0
    va
    cv
    #
    vb
    cv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    vz
    cv
    #
    @6
    c2
    cexp
    co
    #
    @7
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    wa
    #
    vb
    cz
    wrex
    va
    cz
    wrex
    #
    vz
    cab
    @0
    eqid
    #
    @16
    @1
    @3
    cgcd
    co
    #
    c1
    wceq
    #
    @10
    @5
    wceq
    #
    wa
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    vz
    @15
    @21
    @1
    @7
    cgcd
    co
    #
    c1
    wceq
    #
    @10
    @2
    @12
    caddc
    co
    #
    wceq
    #
    wa
    va
    vb
    vx
    vy
    cz
    cz
    @6
    @1
    wceq
    #
    @9
    @23
    @14
    @25
    @26
    @8
    @22
    c1
    @6
    @1
    @7
    cgcd
    oveq1
    eqeq1d
    @26
    @13
    @24
    @10
    @26
    @11
    @2
    @12
    caddc
    @6
    @1
    c2
    cexp
    oveq1
    oveq1d
    eqeq2d
    anbi12d
    @7
    @3
    wceq
    #
    @23
    @19
    @25
    @20
    @27
    @22
    @18
    c1
    @7
    @3
    @1
    cgcd
    oveq2
    eqeq1d
    @27
    @24
    @5
    @10
    @27
    @12
    @4
    @2
    caddc
    @7
    @3
    c2
    cexp
    oveq1
    oveq2d
    eqeq2d
    anbi12d
    cbvrex2v
    abbii
    2sqlem11
    vx
    vy
    vw
    cP
    @0
    @17
    2sqlem2
    sylib
end
