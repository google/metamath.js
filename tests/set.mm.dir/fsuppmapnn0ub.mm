include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "cfn.mm"
include "cv.mm"
include "clt.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "simpr.mm"
include "fsuppimpd.mm"
include "ex.mm"
include "wne.mm"
include "crab.mm"
include "wfn.mm"
include "cvv.mm"
include "elmapfn.mm"
include "adantr.mm"
include "nn0ex.mm"
include "a1i.mm"
include "suppvalfn.mm"
include "syl3anc.mm"
include "eleq1d.mm"
include "wn.mm"
include "rabssnn0fi.mm"
include "nne.mm"
include "imbi2i.mm"
include "ralbii.mm"
include "rexbii.mm"
include "sylbb.mm"
include "syl6bi.mm"
include "syld.mm"

theorem fsuppmapnn0ub
  let vx: setvar x
  let cR: class R
  let vm: setvar m
  let cF: class F
  let cV: class V
  let cZ: class Z

  disjoint F m
  disjoint F x
  disjoint m x
  disjoint V x
  disjoint Z m
  disjoint Z x
  assert |- ( ( F e. ( R ^m NN0 ) /\ Z e. V ) -> ( F finSupp Z -> E. m e. NN0 A. x e. NN0 ( m < x -> ( F ` x ) = Z ) ) )

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
    #
    cF
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    vm
    cv
    vx
    cv
    #
    clt
    wbr
    #
    @6
    cF
    cfv
    #
    cZ
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vm
    cn0
    wrex
    #
    @2
    @3
    @5
    @2
    @3
    wa
    cF
    cZ
    @2
    @3
    simpr
    fsuppimpd
    ex
    @2
    @5
    @8
    cZ
    wne
    #
    vx
    cn0
    crab
    #
    cfn
    wcel
    #
    @12
    @2
    @4
    @14
    cfn
    @2
    cF
    cn0
    wfn
    #
    cn0
    cvv
    wcel
    #
    @1
    @4
    @14
    wceq
    @0
    @16
    @1
    cF
    cR
    cn0
    elmapfn
    adantr
    @17
    @2
    nn0ex
    a1i
    @0
    @1
    simpr
    vx
    cF
    cvv
    cV
    cn0
    cZ
    suppvalfn
    syl3anc
    eleq1d
    @15
    @7
    @13
    wn
    #
    wi
    #
    vx
    cn0
    wral
    #
    vm
    cn0
    wrex
    @12
    @13
    vx
    vm
    rabssnn0fi
    @20
    @11
    vm
    cn0
    @19
    @10
    vx
    cn0
    @18
    @9
    @7
    @8
    cZ
    nne
    imbi2i
    ralbii
    rexbii
    sylbb
    syl6bi
    syld
end
