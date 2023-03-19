include "ccring.mm"
include "wcel.mm"
include "cpridl.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "cidl.mm"
include "wne.mm"
include "ispridlc.mm"
include "biimpa.mm"
include "simp3d.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "eleq1.mm"
include "orbi1d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "orbi2d.mm"
include "rspc2v.mm"
include "com12.mm"
include "expd.mm"
include "3imp2.mm"
include "sylan.mm"

theorem pridlc
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vs: setvar s
  assume ispridlc.1: |- G = ( 1st ` R )
  assume ispridlc.2: |- H = ( 2nd ` R )
  assume ispridlc.3: |- X = ran G


  assert |- ( ( ( R e. CRingOps /\ P e. ( PrIdl ` R ) ) /\ ( A e. X /\ B e. X /\ ( A H B ) e. P ) ) -> ( A e. P \/ B e. P ) )

  proof
    cR
    ccring
    wcel
    #
    cP
    cR
    cpridl
    cfv
    wcel
    #
    wa
    #
    va
    cv
    #
    vb
    cv
    #
    cH
    co
    #
    cP
    wcel
    #
    @3
    cP
    wcel
    #
    @4
    cP
    wcel
    #
    wo
    #
    wi
    #
    vb
    cX
    wral
    va
    cX
    wral
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    cH
    co
    #
    cP
    wcel
    #
    w3a
    cA
    cP
    wcel
    #
    cB
    cP
    wcel
    #
    wo
    #
    @2
    cP
    cR
    cidl
    cfv
    wcel
    #
    cP
    cX
    wne
    #
    @11
    @0
    @1
    @19
    @20
    @11
    w3a
    cP
    cR
    cG
    cH
    cX
    va
    vb
    ispridlc.1
    ispridlc.2
    ispridlc.3
    ispridlc
    biimpa
    simp3d
    @11
    @12
    @13
    @15
    @18
    @11
    @12
    @13
    @15
    @18
    wi
    #
    @12
    @13
    wa
    @11
    @21
    @10
    @21
    cA
    @4
    cH
    co
    #
    cP
    wcel
    #
    @16
    @8
    wo
    #
    wi
    va
    vb
    cA
    cB
    cX
    cX
    @3
    cA
    wceq
    #
    @6
    @23
    @9
    @24
    @25
    @5
    @22
    cP
    @3
    cA
    @4
    cH
    oveq1
    eleq1d
    @25
    @7
    @16
    @8
    @3
    cA
    cP
    eleq1
    orbi1d
    imbi12d
    @4
    cB
    wceq
    #
    @23
    @15
    @24
    @18
    @26
    @22
    @14
    cP
    @4
    cB
    cA
    cH
    oveq2
    eleq1d
    @26
    @8
    @17
    @16
    @4
    cB
    cP
    eleq1
    orbi2d
    imbi12d
    rspc2v
    com12
    expd
    3imp2
    sylan
end
