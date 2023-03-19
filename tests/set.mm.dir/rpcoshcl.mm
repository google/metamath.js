include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "ce.mm"
include "cneg.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "crp.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "coshval.mm"
include "syl.mm"
include "rpefcl.mm"
include "renegcl.mm"
include "rpefcld.mm"
include "rpaddcld.mm"
include "rphalfcld.mm"
include "eqeltrd.mm"

theorem rpcoshcl
  let cA: class A


  assert |- ( A e. RR -> ( cos ` ( _i x. A ) ) e. RR+ )

  proof
    cA
    cr
    wcel
    #
    ci
    cA
    cmul
    co
    ccos
    cfv
    #
    cA
    ce
    cfv
    #
    cA
    cneg
    #
    ce
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    crp
    @0
    cA
    cc
    wcel
    @1
    @6
    wceq
    cA
    recn
    cA
    coshval
    syl
    @0
    @5
    @0
    @2
    @4
    cA
    rpefcl
    @0
    @3
    cA
    renegcl
    rpefcld
    rpaddcld
    rphalfcld
    eqeltrd
end
