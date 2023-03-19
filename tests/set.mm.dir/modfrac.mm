include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cmo.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "crp.mm"
include "wceq.mm"
include "1rp.mm"
include "modval.mm"
include "mpan2.mm"
include "recn.mm"
include "div1d.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "reflcl.mm"
include "recnd.mm"
include "mulid2d.mm"
include "eqtrd.mm"

theorem modfrac
  let cA: class A


  assert |- ( A e. RR -> ( A mod 1 ) = ( A - ( |_ ` A ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    c1
    cmo
    co
    #
    cA
    c1
    cA
    c1
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cA
    cA
    cfl
    cfv
    #
    cmin
    co
    @0
    c1
    crp
    wcel
    @1
    @5
    wceq
    1rp
    cA
    c1
    modval
    mpan2
    @0
    @4
    @6
    cA
    cmin
    @0
    @4
    c1
    @6
    cmul
    co
    @6
    @0
    @3
    @6
    c1
    cmul
    @0
    @2
    cA
    cfl
    @0
    cA
    cA
    recn
    div1d
    fveq2d
    oveq2d
    @0
    @6
    @0
    @6
    cA
    reflcl
    recnd
    mulid2d
    eqtrd
    oveq2d
    eqtrd
end
