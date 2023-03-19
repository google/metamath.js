include "cst.mm"
include "wcel.mm"
include "chil.mm"
include "cort.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c0h.mm"
include "cc0.mm"
include "helch.mm"
include "sto2i.mm"
include "sthil.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "choc1.mm"
include "fveq2i.mm"
include "1m1e0.mm"
include "3eqtr3g.mm"

theorem st0
  let cS: class S


  assert |- ( S e. States -> ( S ` 0H ) = 0 )

  proof
    cS
    cst
    wcel
    #
    chil
    cort
    cfv
    #
    cS
    cfv
    #
    c1
    c1
    cmin
    co
    #
    c0h
    cS
    cfv
    cc0
    @0
    @2
    c1
    chil
    cS
    cfv
    #
    cmin
    co
    @3
    chil
    cS
    helch
    sto2i
    @0
    @4
    c1
    c1
    cmin
    cS
    sthil
    oveq2d
    eqtrd
    @1
    c0h
    cS
    choc1
    fveq2i
    1m1e0
    3eqtr3g
end
