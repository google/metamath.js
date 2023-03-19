include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cv.mm"
include "clt.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "csupp.mm"
include "cc0.mm"
include "cfz.mm"
include "wss.mm"
include "fsuppmapnn0ub.mm"
include "simpllr.mm"
include "simplll.mm"
include "simplr.mm"
include "simpr.mm"
include "suppssfz.mm"
include "ex.mm"
include "reximdva.mm"
include "syld.mm"

theorem fsuppmapnn0fz
  let cR: class R
  let vm: setvar m
  let cF: class F
  let cV: class V
  let cZ: class Z
  let vx: setvar x

  disjoint F m
  disjoint Z m
  disjoint R m
  disjoint V m
  disjoint F x
  disjoint m x
  disjoint V x
  disjoint Z x
  assert |- ( ( F e. ( R ^m NN0 ) /\ Z e. V ) -> ( F finSupp Z -> E. m e. NN0 ( F supp Z ) C_ ( 0 ... m ) ) )

  proof
    cF
    cR
    cn0
    cmap
    co
    wcel
    #
    cZ
    cV
    wcel
    #
    wa
    #
    cF
    cZ
    cfsupp
    wbr
    vm
    cv
    #
    vx
    cv
    #
    clt
    wbr
    @4
    cF
    cfv
    cZ
    wceq
    wi
    vx
    cn0
    wral
    #
    vm
    cn0
    wrex
    cF
    cZ
    csupp
    co
    cc0
    @3
    cfz
    co
    wss
    #
    vm
    cn0
    wrex
    vx
    cR
    vm
    cF
    cV
    cZ
    fsuppmapnn0ub
    @2
    @5
    @6
    vm
    cn0
    @2
    @3
    cn0
    wcel
    #
    wa
    #
    @5
    @6
    @8
    @5
    wa
    vx
    cR
    @3
    cF
    cV
    cZ
    @0
    @1
    @7
    @5
    simpllr
    @0
    @1
    @7
    @5
    simplll
    @2
    @7
    @5
    simplr
    @8
    @5
    simpr
    suppssfz
    ex
    reximdva
    syld
end
