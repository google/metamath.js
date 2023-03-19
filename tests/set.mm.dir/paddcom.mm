include "clat.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cun.mm"
include "cv.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "wrex.mm"
include "crab.mm"
include "wceq.mm"
include "uncom.mm"
include "a1i.mm"
include "wa.mm"
include "cbs.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "sseldd.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simpl3.mm"
include "simprr.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "2rexbidva.mm"
include "rexcom.mm"
include "syl6bb.mm"
include "rabbidv.mm"
include "uneq12d.mm"
include "paddval.mm"
include "3com23.mm"
include "3eqtr4d.mm"

theorem paddcom
  let cA: class A
  let c.pl: class .+
  let cK: class K
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let cB: class B
  let cS: class S
  assume padd0.a: |- A = ( Atoms ` K )
  assume padd0.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. Lat /\ X C_ A /\ Y C_ A ) -> ( X .+ Y ) = ( Y .+ X ) )

  proof
    cK
    clat
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    w3a
    #
    cX
    cY
    cun
    #
    vp
    cv
    #
    vq
    cv
    #
    vr
    cv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cK
    cple
    cfv
    #
    wbr
    #
    vr
    cY
    wrex
    vq
    cX
    wrex
    #
    vp
    cA
    crab
    #
    cun
    cY
    cX
    cun
    #
    @5
    @7
    @6
    @8
    co
    #
    @10
    wbr
    #
    vq
    cX
    wrex
    vr
    cY
    wrex
    #
    vp
    cA
    crab
    #
    cun
    #
    cX
    cY
    c.pl
    co
    cY
    cX
    c.pl
    co
    #
    @3
    @4
    @14
    @13
    @18
    @4
    @14
    wceq
    @3
    cX
    cY
    uncom
    a1i
    @3
    @12
    @17
    vp
    cA
    @3
    @12
    @16
    vr
    cY
    wrex
    vq
    cX
    wrex
    @17
    @3
    @11
    @16
    vq
    vr
    cX
    cY
    @3
    @6
    cX
    wcel
    #
    @7
    cY
    wcel
    #
    wa
    #
    wa
    #
    @9
    @15
    @5
    @10
    @24
    @0
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @25
    wcel
    #
    @9
    @15
    wceq
    @0
    @1
    @2
    @23
    simpl1
    @24
    @6
    cA
    wcel
    @26
    @24
    cX
    cA
    @6
    @0
    @1
    @2
    @23
    simpl2
    @3
    @21
    @22
    simprl
    sseldd
    cA
    @25
    @6
    cK
    @25
    eqid
    #
    padd0.a
    atbase
    syl
    @24
    @7
    cA
    wcel
    @27
    @24
    cY
    cA
    @7
    @0
    @1
    @2
    @23
    simpl3
    @3
    @21
    @22
    simprr
    sseldd
    cA
    @25
    @7
    cK
    @28
    padd0.a
    atbase
    syl
    @25
    @8
    cK
    @6
    @7
    @28
    @8
    eqid
    #
    latjcom
    syl3anc
    breq2d
    2rexbidva
    @16
    vq
    vr
    cX
    cY
    rexcom
    syl6bb
    rabbidv
    uneq12d
    cA
    clat
    c.pl
    @8
    cK
    @10
    cX
    cY
    vr
    vq
    vp
    @10
    eqid
    #
    @29
    padd0.a
    padd0.p
    paddval
    @0
    @2
    @1
    @20
    @19
    wceq
    cA
    clat
    c.pl
    @8
    cK
    @10
    cY
    cX
    vq
    vr
    vp
    @30
    @29
    padd0.a
    padd0.p
    paddval
    3com23
    3eqtr4d
end
