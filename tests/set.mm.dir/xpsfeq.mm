include "c2o.mm"
include "wfn.mm"
include "c0.mm"
include "cfv.mm"
include "csn.mm"
include "c1o.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "xpscfn.mm"
include "mp2an.mm"
include "a1i.mm"
include "id.mm"
include "cv.mm"
include "wceq.mm"
include "wo.mm"
include "cpr.mm"
include "elpri.mm"
include "df2o3.mm"
include "eleq2s.mm"
include "xpsc0.mm"
include "ax-mp.mm"
include "fveq2.mm"
include "3eqtr4a.mm"
include "xpsc1.mm"
include "jaoi.mm"
include "syl.mm"
include "adantl.mm"
include "eqfnfvd.mm"

theorem xpsfeq
  let cG: class G
  let cA: class A
  let vk: setvar k
  let cB: class B
  let cX: class X
  let cY: class Y


  assert |- ( G Fn 2o -> `' ( { ( G ` (/) ) } +c { ( G ` 1o ) } ) = G )

  proof
    cG
    c2o
    wfn
    #
    vk
    c2o
    c0
    cG
    cfv
    #
    csn
    c1o
    cG
    cfv
    #
    csn
    ccda
    co
    ccnv
    #
    cG
    @3
    c2o
    wfn
    #
    @0
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    @4
    c0
    cG
    fvex
    #
    c1o
    cG
    fvex
    #
    @1
    @2
    cvv
    cvv
    xpscfn
    mp2an
    a1i
    @0
    id
    vk
    cv
    #
    c2o
    wcel
    #
    @9
    @3
    cfv
    #
    @9
    cG
    cfv
    #
    wceq
    #
    @0
    @10
    @9
    c0
    wceq
    #
    @9
    c1o
    wceq
    #
    wo
    #
    @13
    @16
    @9
    c0
    c1o
    cpr
    c2o
    @9
    c0
    c1o
    elpri
    df2o3
    eleq2s
    @14
    @13
    @15
    @14
    c0
    @3
    cfv
    #
    @1
    @11
    @12
    @5
    @17
    @1
    wceq
    @7
    @1
    @2
    cvv
    xpsc0
    ax-mp
    @9
    c0
    @3
    fveq2
    @9
    c0
    cG
    fveq2
    3eqtr4a
    @15
    c1o
    @3
    cfv
    #
    @2
    @11
    @12
    @6
    @18
    @2
    wceq
    @8
    @1
    @2
    cvv
    xpsc1
    ax-mp
    @9
    c1o
    @3
    fveq2
    @9
    c1o
    cG
    fveq2
    3eqtr4a
    jaoi
    syl
    adantl
    eqfnfvd
end
