include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wceq.mm"
include "wo.mm"
include "co.mm"
include "wb.mm"
include "neanior.mm"
include "bicomi.mm"
include "con1bii.mm"
include "cv.mm"
include "cjn.mm"
include "cfv.mm"
include "cple.mm"
include "wbr.mm"
include "wrex.mm"
include "eqid.mm"
include "elpadd.mm"
include "rex0.mm"
include "rexeq.mm"
include "mtbiri.mm"
include "a1i.mm"
include "nrex.mm"
include "rexbidv.mm"
include "jaoi.mm"
include "intnand.mm"
include "biorf.mm"
include "syl.mm"
include "orcom.mm"
include "syl6rbb.mm"
include "sylan9bb.mm"
include "sylan2b.mm"

theorem elpadd0
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cK: class K
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume padd0.a: |- A = ( Atoms ` K )
  assume padd0.p: |- .+ = ( +P ` K )


  assert |- ( ( ( K e. B /\ X C_ A /\ Y C_ A ) /\ -. ( X =/= (/) /\ Y =/= (/) ) ) -> ( S e. ( X .+ Y ) <-> ( S e. X \/ S e. Y ) ) )

  proof
    cX
    c0
    wne
    cY
    c0
    wne
    wa
    #
    wn
    cK
    cB
    wcel
    cX
    cA
    wss
    cY
    cA
    wss
    w3a
    #
    cX
    c0
    wceq
    #
    cY
    c0
    wceq
    #
    wo
    #
    cS
    cX
    cY
    c.pl
    co
    wcel
    #
    cS
    cX
    wcel
    cS
    cY
    wcel
    wo
    #
    wb
    @4
    @0
    @0
    @4
    wn
    cX
    c0
    cY
    c0
    neanior
    bicomi
    con1bii
    @1
    @5
    @6
    cS
    cA
    wcel
    #
    cS
    vq
    cv
    #
    vr
    cv
    cK
    cjn
    cfv
    #
    co
    cK
    cple
    cfv
    #
    wbr
    #
    vr
    cY
    wrex
    #
    vq
    cX
    wrex
    #
    wa
    #
    wo
    #
    @4
    @6
    cA
    cB
    c.pl
    cS
    @9
    cK
    @10
    cX
    cY
    vr
    vq
    @10
    eqid
    @9
    eqid
    padd0.a
    padd0.p
    elpadd
    @4
    @6
    @14
    @6
    wo
    #
    @15
    @4
    @14
    wn
    @6
    @16
    wb
    @4
    @13
    @7
    @2
    @13
    wn
    @3
    @2
    @13
    @12
    vq
    c0
    wrex
    @12
    vq
    rex0
    @12
    vq
    cX
    c0
    rexeq
    mtbiri
    @3
    @13
    @11
    vr
    c0
    wrex
    #
    vq
    cX
    wrex
    @17
    vq
    cX
    @17
    wn
    @8
    cX
    wcel
    @11
    vr
    rex0
    a1i
    nrex
    @3
    @12
    @17
    vq
    cX
    @11
    vr
    cY
    c0
    rexeq
    rexbidv
    mtbiri
    jaoi
    intnand
    @14
    @6
    biorf
    syl
    @14
    @6
    orcom
    syl6rbb
    sylan9bb
    sylan2b
end
