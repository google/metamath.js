include "clo.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wb.mm"
include "ch0o.mm"
include "cif.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "0lnop.mm"
include "elimel.mm"
include "lnopeqi.mm"
include "dedth2h.mm"

theorem lnopeq
  let vx: setvar x
  let cT: class T
  let cU: class U

  disjoint T x
  disjoint U x
  assert |- ( ( T e. LinOp /\ U e. LinOp ) -> ( A. x e. ~H ( ( T ` x ) .ih x ) = ( ( U ` x ) .ih x ) <-> T = U ) )

  proof
    cT
    clo
    wcel
    #
    cU
    clo
    wcel
    #
    vx
    cv
    #
    cT
    cfv
    #
    @2
    csp
    co
    #
    @2
    cU
    cfv
    #
    @2
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    #
    cT
    cU
    wceq
    #
    wb
    @2
    @0
    cT
    ch0o
    cif
    #
    cfv
    #
    @2
    csp
    co
    #
    @6
    wceq
    #
    vx
    chil
    wral
    #
    @10
    cU
    wceq
    #
    wb
    @12
    @2
    @1
    cU
    ch0o
    cif
    #
    cfv
    #
    @2
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    #
    @10
    @16
    wceq
    #
    wb
    cT
    cU
    ch0o
    ch0o
    cT
    @10
    wceq
    #
    @8
    @14
    @9
    @15
    @22
    @7
    @13
    vx
    chil
    @22
    @4
    @12
    @6
    @22
    @3
    @11
    @2
    csp
    @2
    cT
    @10
    fveq1
    oveq1d
    eqeq1d
    ralbidv
    cT
    @10
    cU
    eqeq1
    bibi12d
    cU
    @16
    wceq
    #
    @14
    @20
    @15
    @21
    @23
    @13
    @19
    vx
    chil
    @23
    @6
    @18
    @12
    @23
    @5
    @17
    @2
    csp
    @2
    cU
    @16
    fveq1
    oveq1d
    eqeq2d
    ralbidv
    cU
    @16
    @10
    eqeq2
    bibi12d
    vx
    @10
    @16
    cT
    ch0o
    clo
    0lnop
    elimel
    cU
    ch0o
    clo
    0lnop
    elimel
    lnopeqi
    dedth2h
end
