include "crg.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "wa.mm"
include "wceq.mm"
include "cbs.mm"
include "wf1.mm"
include "wb.mm"
include "eqid.mm"
include "ply1sclf1.mm"
include "adantr.mm"
include "simpr.mm"
include "ring0cl.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "biimpd.mm"
include "necon3d.mm"
include "3impia.mm"
include "ply1scl0.mm"
include "3ad2ant1.mm"
include "neeqtrd.mm"

theorem ply1scln0
  let cA: class A
  let cP: class P
  let cR: class R
  let cK: class K
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume ply1scl.p: |- P = ( Poly1 ` R )
  assume ply1scl.a: |- A = ( algSc ` P )
  assume ply1scl0.z: |- .0. = ( 0g ` R )
  assume ply1scl0.y: |- Y = ( 0g ` P )
  assume ply1scln0.k: |- K = ( Base ` R )


  assert |- ( ( R e. Ring /\ X e. K /\ X =/= .0. ) -> ( A ` X ) =/= Y )

  proof
    cR
    crg
    wcel
    #
    cX
    cK
    wcel
    #
    cX
    c.0
    wne
    #
    w3a
    cX
    cA
    cfv
    #
    c.0
    cA
    cfv
    #
    cY
    @0
    @1
    @2
    @3
    @4
    wne
    @0
    @1
    wa
    #
    @3
    @4
    cX
    c.0
    @5
    @3
    @4
    wceq
    #
    cX
    c.0
    wceq
    #
    @5
    cK
    cP
    cbs
    cfv
    #
    cA
    wf1
    #
    @1
    c.0
    cK
    wcel
    #
    @6
    @7
    wb
    @0
    @9
    @1
    cA
    @8
    cP
    cR
    cK
    ply1scl.p
    ply1scl.a
    ply1scln0.k
    @8
    eqid
    ply1sclf1
    adantr
    @0
    @1
    simpr
    @0
    @10
    @1
    cK
    cR
    c.0
    ply1scln0.k
    ply1scl0.z
    ring0cl
    adantr
    cK
    @8
    cX
    c.0
    cA
    f1fveq
    syl12anc
    biimpd
    necon3d
    3impia
    @0
    @1
    @4
    cY
    wceq
    @2
    cA
    cP
    cR
    cY
    c.0
    ply1scl.p
    ply1scl.a
    ply1scl0.z
    ply1scl0.y
    ply1scl0
    3ad2ant1
    neeqtrd
end
