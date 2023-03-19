include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "wf.mm"
include "wfn.mm"
include "cfz.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "swrd0f.mm"
include "mpdan.mm"
include "ffn.mm"
include "syl.mm"
include "wrdfn.mm"
include "cv.mm"
include "wa.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "simpl.mm"
include "0elfz.mm"
include "adantr.mm"
include "nn0cnd.mm"
include "subid1d.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "swrdfv.mm"
include "syl31anc.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "addid1d.mm"
include "adantl.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eqfnfvd.mm"

theorem swrdid
  let cA: class A
  let cS: class S
  let vx: setvar x


  assert |- ( S e. Word A -> ( S substr <. 0 , ( # ` S ) >. ) = S )

  proof
    cS
    cA
    cword
    wcel
    #
    vx
    cc0
    cS
    chash
    cfv
    #
    cfzo
    co
    #
    cS
    cc0
    @1
    cop
    csubstr
    co
    #
    cS
    @0
    @2
    cA
    @3
    wf
    #
    @3
    @2
    wfn
    @0
    @1
    cc0
    @1
    cfz
    co
    #
    wcel
    #
    @4
    @0
    @1
    cn0
    wcel
    #
    @6
    cA
    cS
    lencl
    #
    @1
    nn0fz0
    sylib
    #
    @1
    cA
    cS
    swrd0f
    mpdan
    @2
    cA
    @3
    ffn
    syl
    cA
    cS
    wrdfn
    @0
    vx
    cv
    #
    @2
    wcel
    #
    wa
    #
    @10
    @3
    cfv
    #
    @10
    cc0
    caddc
    co
    #
    cS
    cfv
    #
    @10
    cS
    cfv
    @12
    @0
    cc0
    @5
    wcel
    #
    @6
    @10
    cc0
    @1
    cc0
    cmin
    co
    #
    cfzo
    co
    #
    wcel
    #
    @13
    @15
    wceq
    @0
    @11
    simpl
    @0
    @16
    @11
    @0
    @7
    @16
    @8
    @1
    0elfz
    syl
    adantr
    @0
    @6
    @11
    @9
    adantr
    @0
    @19
    @11
    @0
    @18
    @2
    @10
    @0
    @17
    @1
    cc0
    cfzo
    @0
    @1
    @0
    @1
    @8
    nn0cnd
    subid1d
    oveq2d
    eleq2d
    biimpar
    cA
    cS
    cc0
    @1
    @10
    swrdfv
    syl31anc
    @12
    @14
    @10
    cS
    @11
    @14
    @10
    wceq
    @0
    @11
    @10
    @11
    @10
    @10
    cc0
    @1
    elfzoelz
    zcnd
    addid1d
    adantl
    fveq2d
    eqtrd
    eqfnfvd
end
