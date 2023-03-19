include "ctop.mm"
include "wcel.mm"
include "cxko.mm"
include "co.mm"
include "crn.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "wceq.mm"
include "cv.mm"
include "crest.mm"
include "ccmp.mm"
include "cuni.mm"
include "cpw.mm"
include "crab.mm"
include "cima.mm"
include "wss.mm"
include "ccn.mm"
include "cmpt2.mm"
include "wa.mm"
include "simpr.mm"
include "unieqd.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "rabeqbidv.mm"
include "simpl.mm"
include "oveq12d.mm"
include "rabeq.mm"
include "syl.mm"
include "mpt2eq123dv.mm"
include "rneqd.mm"
include "fveq2d.mm"
include "df-xko.mm"
include "fvex.mm"
include "ovmpt2a.mm"
include "ancoms.mm"

theorem xkoval
  let vx: setvar x
  let vv: setvar v
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vk: setvar k
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vr: setvar r
  assume xkoval.x: |- X = U. R
  assume xkoval.k: |- K = { x e. ~P X | ( R |`t x ) e. Comp }
  assume xkoval.t: |- T = ( k e. K , v e. S |-> { f e. ( R Cn S ) | ( f " k ) C_ v } )

  disjoint k v
  disjoint K k
  disjoint K v
  disjoint f k
  disjoint f v
  disjoint f x
  disjoint R f
  disjoint k x
  disjoint R k
  disjoint v x
  disjoint R v
  disjoint R x
  disjoint S f
  disjoint S k
  disjoint S v
  disjoint S x
  disjoint X k
  disjoint X x
  disjoint k s
  disjoint s v
  disjoint K s
  disjoint f r
  disjoint f s
  disjoint k r
  disjoint r s
  disjoint r v
  disjoint r x
  disjoint R r
  disjoint s x
  disjoint R s
  disjoint S r
  disjoint S s
  disjoint T r
  disjoint T s
  assert |- ( ( R e. Top /\ S e. Top ) -> ( S ^ko R ) = ( topGen ` ( fi ` ran T ) ) )

  proof
    cS
    ctop
    wcel
    cR
    ctop
    wcel
    cS
    cR
    cxko
    co
    cT
    crn
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    wceq
    vs
    vr
    cS
    cR
    ctop
    ctop
    vk
    vv
    vr
    cv
    #
    vx
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    vx
    @3
    cuni
    #
    cpw
    #
    crab
    #
    vs
    cv
    #
    vf
    cv
    vk
    cv
    cima
    vv
    cv
    wss
    #
    vf
    @3
    @10
    ccn
    co
    #
    crab
    #
    cmpt2
    #
    crn
    #
    cfi
    cfv
    #
    ctg
    cfv
    @2
    cxko
    @10
    cS
    wceq
    #
    @3
    cR
    wceq
    #
    wa
    #
    @16
    @1
    ctg
    @19
    @15
    @0
    cfi
    @19
    @14
    cT
    @19
    @14
    vk
    vv
    cK
    cS
    @11
    vf
    cR
    cS
    ccn
    co
    #
    crab
    #
    cmpt2
    cT
    @19
    vk
    vv
    @9
    @10
    @13
    cK
    cS
    @21
    @19
    @9
    cR
    @4
    crest
    co
    #
    ccmp
    wcel
    #
    vx
    cX
    cpw
    #
    crab
    cK
    @19
    @6
    @23
    vx
    @8
    @24
    @19
    @7
    cX
    @19
    @7
    cR
    cuni
    cX
    @19
    @3
    cR
    @17
    @18
    simpr
    #
    unieqd
    xkoval.x
    syl6eqr
    pweqd
    @19
    @5
    @22
    ccmp
    @19
    @3
    cR
    @4
    crest
    @25
    oveq1d
    eleq1d
    rabeqbidv
    xkoval.k
    syl6eqr
    @17
    @18
    simpl
    #
    @19
    @12
    @20
    wceq
    @13
    @21
    wceq
    @19
    @3
    cR
    @10
    cS
    ccn
    @25
    @26
    oveq12d
    @11
    vf
    @12
    @20
    rabeq
    syl
    mpt2eq123dv
    xkoval.t
    syl6eqr
    rneqd
    fveq2d
    fveq2d
    vx
    vv
    vf
    vk
    vs
    vr
    df-xko
    @1
    ctg
    fvex
    ovmpt2a
    ancoms
end
