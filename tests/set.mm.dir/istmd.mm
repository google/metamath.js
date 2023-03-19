include "cmnd.mm"
include "ctps.mm"
include "cin.mm"
include "wcel.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "wa.mm"
include "ctmd.mm"
include "w3a.mm"
include "elin.mm"
include "anbi1i.mm"
include "cv.mm"
include "cplusf.mm"
include "cfv.mm"
include "ctopn.mm"
include "wsbc.mm"
include "wceq.mm"
include "cvv.mm"
include "fvexd.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "id.mm"
include "fveq2.mm"
include "sylan9eqr.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "sbcied.mm"
include "df-tmd.mm"
include "elrab2.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem istmd
  let cF: class F
  let cG: class G
  let cJ: class J
  let vf: setvar f
  let vj: setvar j
  assume istmd.1: |- F = ( +f ` G )
  assume istmd.2: |- J = ( TopOpen ` G )


  assert |- ( G e. TopMnd <-> ( G e. Mnd /\ G e. TopSp /\ F e. ( ( J tX J ) Cn J ) ) )

  proof
    cG
    cmnd
    ctps
    cin
    #
    wcel
    #
    cF
    cJ
    cJ
    ctx
    co
    #
    cJ
    ccn
    co
    #
    wcel
    #
    wa
    cG
    cmnd
    wcel
    #
    cG
    ctps
    wcel
    #
    wa
    #
    @4
    wa
    cG
    ctmd
    wcel
    @5
    @6
    @4
    w3a
    @1
    @7
    @4
    cG
    cmnd
    ctps
    elin
    anbi1i
    vf
    cv
    #
    cplusf
    cfv
    #
    vj
    cv
    #
    @10
    ctx
    co
    #
    @10
    ccn
    co
    #
    wcel
    #
    vj
    @8
    ctopn
    cfv
    #
    wsbc
    @4
    vf
    cG
    @0
    ctmd
    @8
    cG
    wceq
    #
    @13
    @4
    vj
    @14
    cvv
    @15
    @8
    ctopn
    fvexd
    @15
    @10
    @14
    wceq
    #
    wa
    #
    @9
    cF
    @12
    @3
    @17
    @9
    cG
    cplusf
    cfv
    cF
    @17
    @8
    cG
    cplusf
    @15
    @16
    simpl
    fveq2d
    istmd.1
    syl6eqr
    @17
    @11
    @2
    @10
    cJ
    ccn
    @17
    @10
    cJ
    @10
    cJ
    ctx
    @16
    @15
    @10
    @14
    cJ
    @16
    id
    @15
    @14
    cG
    ctopn
    cfv
    cJ
    @8
    cG
    ctopn
    fveq2
    istmd.2
    syl6eqr
    sylan9eqr
    #
    @18
    oveq12d
    @18
    oveq12d
    eleq12d
    sbcied
    vf
    vj
    df-tmd
    elrab2
    @5
    @6
    @4
    df-3an
    3bitr4i
end
