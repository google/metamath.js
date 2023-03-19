include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cmo.mm"
include "co.mm"
include "cmin.mm"
include "cfl.mm"
include "cfv.mm"
include "modfrac.mm"
include "oveq2d.mm"
include "recn.mm"
include "reflcl.mm"
include "recnd.mm"
include "nncand.mm"
include "eqtr2d.mm"

theorem flmod
  let cA: class A


  assert |- ( A e. RR -> ( |_ ` A ) = ( A - ( A mod 1 ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cA
    c1
    cmo
    co
    #
    cmin
    co
    cA
    cA
    cA
    cfl
    cfv
    #
    cmin
    co
    #
    cmin
    co
    @2
    @0
    @1
    @3
    cA
    cmin
    cA
    modfrac
    oveq2d
    @0
    cA
    @2
    cA
    recn
    @0
    @2
    cA
    reflcl
    recnd
    nncand
    eqtr2d
end
