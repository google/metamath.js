include "cn0.mm"
include "wcel.mm"
include "cfallfac.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "c1.mm"
include "cc0.mm"
include "cfz.mm"
include "wceq.mm"
include "nn0fz0.mm"
include "fallfacval4.mm"
include "sylbi.mm"
include "nn0cn.mm"
include "subidd.mm"
include "fveq2d.mm"
include "fac0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "faccl.mm"
include "nncnd.mm"
include "div1d.mm"
include "3eqtrd.mm"

theorem fallfacfac
  let cN: class N


  assert |- ( N e. NN0 -> ( N FallFac N ) = ( ! ` N ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cN
    cfallfac
    co
    #
    cN
    cfa
    cfv
    #
    cN
    cN
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    @2
    c1
    cdiv
    co
    @2
    @0
    cN
    cc0
    cN
    cfz
    co
    wcel
    @1
    @5
    wceq
    cN
    nn0fz0
    cN
    cN
    fallfacval4
    sylbi
    @0
    @4
    c1
    @2
    cdiv
    @0
    @4
    cc0
    cfa
    cfv
    c1
    @0
    @3
    cc0
    cfa
    @0
    cN
    cN
    nn0cn
    subidd
    fveq2d
    fac0
    syl6eq
    oveq2d
    @0
    @2
    @0
    @2
    cN
    faccl
    nncnd
    div1d
    3eqtrd
end
