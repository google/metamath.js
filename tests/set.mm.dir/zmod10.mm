include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cmo.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cc0.mm"
include "cr.mm"
include "wceq.mm"
include "zre.mm"
include "modfrac.mm"
include "syl.mm"
include "flid.mm"
include "oveq2d.mm"
include "zcn.mm"
include "subidd.mm"
include "3eqtrd.mm"

theorem zmod10
  let cN: class N


  assert |- ( N e. ZZ -> ( N mod 1 ) = 0 )

  proof
    cN
    cz
    wcel
    #
    cN
    c1
    cmo
    co
    #
    cN
    cN
    cfl
    cfv
    #
    cmin
    co
    #
    cN
    cN
    cmin
    co
    cc0
    @0
    cN
    cr
    wcel
    @1
    @3
    wceq
    cN
    zre
    cN
    modfrac
    syl
    @0
    @2
    cN
    cN
    cmin
    cN
    flid
    oveq2d
    @0
    cN
    cN
    zcn
    subidd
    3eqtrd
end
