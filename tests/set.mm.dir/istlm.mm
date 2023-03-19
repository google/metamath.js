include "ctmd.mm"
include "clmod.mm"
include "cin.mm"
include "wcel.mm"
include "ctrg.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "w3a.mm"
include "ctlm.mm"
include "anass.mm"
include "df-3an.mm"
include "elin.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "cscaf.mm"
include "ctopn.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "df-tlm.mm"
include "elrab2.mm"
include "3bitr4ri.mm"

theorem istlm
  let c.x: class .x.
  let cF: class F
  let cJ: class J
  let cK: class K
  let cW: class W
  let vw: setvar w
  assume istlm.s: |- .x. = ( .sf ` W )
  assume istlm.j: |- J = ( TopOpen ` W )
  assume istlm.f: |- F = ( Scalar ` W )
  assume istlm.k: |- K = ( TopOpen ` F )


  assert |- ( W e. TopMod <-> ( ( W e. TopMnd /\ W e. LMod /\ F e. TopRing ) /\ .x. e. ( ( K tX J ) Cn J ) ) )

  proof
    cW
    ctmd
    clmod
    cin
    #
    wcel
    #
    cF
    ctrg
    wcel
    #
    wa
    #
    c.x
    cK
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
    @1
    @2
    @6
    wa
    #
    wa
    cW
    ctmd
    wcel
    #
    cW
    clmod
    wcel
    #
    @2
    w3a
    #
    @6
    wa
    cW
    ctlm
    wcel
    @1
    @2
    @6
    anass
    @10
    @3
    @6
    @10
    @8
    @9
    wa
    #
    @2
    wa
    @3
    @8
    @9
    @2
    df-3an
    @1
    @11
    @2
    cW
    ctmd
    clmod
    elin
    anbi1i
    bitr4i
    anbi1i
    vw
    cv
    #
    csca
    cfv
    #
    ctrg
    wcel
    #
    @12
    cscaf
    cfv
    #
    @13
    ctopn
    cfv
    #
    @12
    ctopn
    cfv
    #
    ctx
    co
    #
    @17
    ccn
    co
    #
    wcel
    #
    wa
    @7
    vw
    cW
    @0
    ctlm
    @12
    cW
    wceq
    #
    @14
    @2
    @20
    @6
    @21
    @13
    cF
    ctrg
    @21
    @13
    cW
    csca
    cfv
    cF
    @12
    cW
    csca
    fveq2
    istlm.f
    syl6eqr
    #
    eleq1d
    @21
    @15
    c.x
    @19
    @5
    @21
    @15
    cW
    cscaf
    cfv
    c.x
    @12
    cW
    cscaf
    fveq2
    istlm.s
    syl6eqr
    @21
    @18
    @4
    @17
    cJ
    ccn
    @21
    @16
    cK
    @17
    cJ
    ctx
    @21
    @16
    cF
    ctopn
    cfv
    cK
    @21
    @13
    cF
    ctopn
    @22
    fveq2d
    istlm.k
    syl6eqr
    @21
    @17
    cW
    ctopn
    cfv
    cJ
    @12
    cW
    ctopn
    fveq2
    istlm.j
    syl6eqr
    #
    oveq12d
    @23
    oveq12d
    eleq12d
    anbi12d
    vw
    df-tlm
    elrab2
    3bitr4ri
end
