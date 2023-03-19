include "cn0.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "cv.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "wcel.mm"
include "wceq.mm"
include "csn.mm"
include "cmpt.mm"
include "elmapi.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "cvv.mm"
include "cc.mm"
include "crg.mm"
include "cnring.mm"
include "ringmnd.mm"
include "mp1i.mm"
include "0ex.mm"
include "a1i.mm"
include "wf.mm"
include "snid.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "nn0cnd.mm"
include "cnfldbas.mm"
include "fveq2.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "df1o2.mm"
include "oveq2i.mm"
include "eleq2s.mm"
include "eqcomd.mm"
include "mpteq2ia.mm"

theorem tdeglem2
  let vh: setvar h
  let vx: setvar x


  assert |- ( h e. ( NN0 ^m 1o ) |-> ( h ` (/) ) ) = ( h e. ( NN0 ^m 1o ) |-> ( CCfld gsum h ) )

  proof
    vh
    cn0
    c1o
    cmap
    co
    #
    c0
    vh
    cv
    #
    cfv
    #
    ccnfld
    @1
    cgsu
    co
    #
    @1
    @0
    wcel
    @3
    @2
    @3
    @2
    wceq
    @1
    cn0
    c0
    csn
    #
    cmap
    co
    #
    @0
    @1
    @5
    wcel
    #
    @3
    ccnfld
    vx
    @4
    vx
    cv
    #
    @1
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    @2
    @6
    @1
    @9
    ccnfld
    cgsu
    @6
    vx
    @4
    cn0
    @1
    @1
    cn0
    @4
    elmapi
    #
    feqmptd
    oveq2d
    @6
    ccnfld
    cmnd
    wcel
    #
    c0
    cvv
    wcel
    #
    @2
    cc
    wcel
    @10
    @2
    wceq
    ccnfld
    crg
    wcel
    @12
    @6
    cnring
    ccnfld
    ringmnd
    mp1i
    @13
    @6
    0ex
    a1i
    @6
    @2
    @6
    @4
    cn0
    @1
    wf
    c0
    @4
    wcel
    @2
    cn0
    wcel
    @11
    c0
    0ex
    snid
    @4
    cn0
    c0
    @1
    ffvelrn
    sylancl
    nn0cnd
    @8
    cc
    @2
    vx
    ccnfld
    c0
    cvv
    cnfldbas
    @7
    c0
    @1
    fveq2
    gsumsn
    syl3anc
    eqtrd
    c1o
    @4
    cn0
    cmap
    df1o2
    oveq2i
    eleq2s
    eqcomd
    mpteq2ia
end
