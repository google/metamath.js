include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "wo.mm"
include "cjn.mm"
include "cfv.mm"
include "cple.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "ssel.mm"
include "orim1d.mm"
include "ssrexv.mm"
include "anim2d.mm"
include "orim12d.mm"
include "adantl.mm"
include "wb.mm"
include "simpl1.mm"
include "sstr.mm"
include "3ad2antr2.mm"
include "ancoms.mm"
include "simpl3.mm"
include "eqid.mm"
include "elpadd.mm"
include "syl3anc.mm"
include "adantr.mm"
include "3imtr4d.mm"
include "ssrdv.mm"
include "ex.mm"

theorem paddss1
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let cS: class S
  assume padd0.a: |- A = ( Atoms ` K )
  assume padd0.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. B /\ Y C_ A /\ Z C_ A ) -> ( X C_ Y -> ( X .+ Z ) C_ ( Y .+ Z ) ) )

  proof
    cK
    cB
    wcel
    #
    cY
    cA
    wss
    #
    cZ
    cA
    wss
    #
    w3a
    #
    cX
    cY
    wss
    #
    cX
    cZ
    c.pl
    co
    #
    cY
    cZ
    c.pl
    co
    #
    wss
    @3
    @4
    wa
    #
    vp
    @5
    @6
    @7
    vp
    cv
    #
    cX
    wcel
    #
    @8
    cZ
    wcel
    #
    wo
    #
    @8
    cA
    wcel
    #
    @8
    vq
    cv
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
    vr
    cZ
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
    @8
    cY
    wcel
    #
    @10
    wo
    #
    @12
    @15
    vq
    cY
    wrex
    #
    wa
    #
    wo
    #
    @8
    @5
    wcel
    #
    @8
    @6
    wcel
    #
    @4
    @18
    @23
    wi
    @3
    @4
    @11
    @20
    @17
    @22
    @4
    @9
    @19
    @10
    cX
    cY
    @8
    ssel
    orim1d
    @4
    @16
    @21
    @12
    @15
    vq
    cX
    cY
    ssrexv
    anim2d
    orim12d
    adantl
    @7
    @0
    cX
    cA
    wss
    #
    @2
    @24
    @18
    wb
    @0
    @1
    @2
    @4
    simpl1
    @4
    @3
    @26
    @4
    @0
    @1
    @26
    @2
    cX
    cY
    cA
    sstr
    3ad2antr2
    ancoms
    @0
    @1
    @2
    @4
    simpl3
    cA
    cB
    c.pl
    @8
    @13
    cK
    @14
    cX
    cZ
    vr
    vq
    @14
    eqid
    #
    @13
    eqid
    #
    padd0.a
    padd0.p
    elpadd
    syl3anc
    @3
    @25
    @23
    wb
    @4
    cA
    cB
    c.pl
    @8
    @13
    cK
    @14
    cY
    cZ
    vr
    vq
    @27
    @28
    padd0.a
    padd0.p
    elpadd
    adantr
    3imtr4d
    ssrdv
    ex
end
