include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cc0.mm"
include "creps.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "c1.mm"
include "cmin.mm"
include "cv.mm"
include "cmpt.mm"
include "creverse.mm"
include "repswlen.mm"
include "oveq2d.mm"
include "mpteq1d.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr.mm"
include "adantr.mm"
include "oveq1d.mm"
include "ubmelm1fzo.mm"
include "cz.mm"
include "wi.mm"
include "elfzoelz.mm"
include "cc.mm"
include "nn0cn.mm"
include "ad2antll.mm"
include "zcn.mm"
include "1cnd.mm"
include "sub32d.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "ex.mm"
include "syl.mm"
include "mpid.mm"
include "impcom.mm"
include "eqeltrd.mm"
include "repswsymb.mm"
include "syl3anc.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "cvv.mm"
include "ovex.mm"
include "revval.mm"
include "mp1i.mm"
include "reps.mm"
include "3eqtr4d.mm"

theorem repswrevw
  let cS: class S
  let cN: class N
  let cV: class V
  let vx: setvar x


  assert |- ( ( S e. V /\ N e. NN0 ) -> ( reverse ` ( S repeatS N ) ) = ( S repeatS N ) )

  proof
    cS
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    vx
    cc0
    cS
    cN
    creps
    co
    #
    chash
    cfv
    #
    cfzo
    co
    #
    @4
    c1
    cmin
    co
    #
    vx
    cv
    #
    cmin
    co
    #
    @3
    cfv
    #
    cmpt
    #
    vx
    cc0
    cN
    cfzo
    co
    #
    cS
    cmpt
    #
    @3
    creverse
    cfv
    #
    @3
    @2
    @10
    vx
    @11
    @9
    cmpt
    @12
    @2
    vx
    @5
    @11
    @9
    @2
    @4
    cN
    cc0
    cfzo
    cS
    cN
    cV
    repswlen
    #
    oveq2d
    mpteq1d
    @2
    vx
    @11
    @9
    cS
    @2
    @7
    @11
    wcel
    #
    wa
    #
    @0
    @1
    @8
    @11
    wcel
    @9
    cS
    wceq
    @0
    @1
    @15
    simpll
    @0
    @1
    @15
    simplr
    @16
    @8
    cN
    c1
    cmin
    co
    #
    @7
    cmin
    co
    #
    @11
    @16
    @6
    @17
    @7
    cmin
    @16
    @4
    cN
    c1
    cmin
    @2
    @4
    cN
    wceq
    @15
    @14
    adantr
    oveq1d
    oveq1d
    @15
    @2
    @18
    @11
    wcel
    #
    @15
    @2
    cN
    @7
    cmin
    co
    c1
    cmin
    co
    #
    @11
    wcel
    #
    @19
    @7
    cN
    ubmelm1fzo
    @15
    @7
    cz
    wcel
    #
    @2
    @21
    @19
    wi
    #
    wi
    @7
    cc0
    cN
    elfzoelz
    @22
    @2
    @23
    @22
    @2
    wa
    #
    @21
    @19
    @24
    @20
    @18
    @11
    @24
    cN
    @7
    c1
    @1
    cN
    cc
    wcel
    @22
    @0
    cN
    nn0cn
    ad2antll
    @22
    @7
    cc
    wcel
    @2
    @7
    zcn
    adantr
    @24
    1cnd
    sub32d
    eleq1d
    biimpd
    ex
    syl
    mpid
    impcom
    eqeltrd
    cS
    @8
    cN
    cV
    repswsymb
    syl3anc
    mpteq2dva
    eqtrd
    @3
    cvv
    wcel
    @13
    @10
    wceq
    @2
    cS
    cN
    creps
    ovex
    vx
    cvv
    @3
    revval
    mp1i
    vx
    cS
    cN
    cV
    reps
    3eqtr4d
end
