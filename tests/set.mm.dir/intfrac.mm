include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "cmo.mm"
include "co.mm"
include "caddc.mm"
include "cmin.mm"
include "modfrac.mm"
include "oveq2d.mm"
include "reflcl.mm"
include "recnd.mm"
include "recn.mm"
include "pncan3d.mm"
include "eqtr2d.mm"

theorem intfrac
  let cA: class A


  assert |- ( A e. RR -> A = ( ( |_ ` A ) + ( A mod 1 ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cfl
    cfv
    #
    cA
    c1
    cmo
    co
    #
    caddc
    co
    @1
    cA
    @1
    cmin
    co
    #
    caddc
    co
    cA
    @0
    @2
    @3
    @1
    caddc
    cA
    modfrac
    oveq2d
    @0
    @1
    cA
    @0
    @1
    cA
    reflcl
    recnd
    cA
    recn
    pncan3d
    eqtr2d
end
