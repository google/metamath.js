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
include "orim2d.mm"
include "ssrexv.mm"
include "reximdv.mm"
include "anim2d.mm"
include "orim12d.mm"
include "adantl.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl3.mm"
include "sstr.mm"
include "3ad2antr2.mm"
include "ancoms.mm"
include "eqid.mm"
include "elpadd.mm"
include "syl3anc.mm"
include "simpl2.mm"
include "3imtr4d.mm"
include "ssrdv.mm"
include "ex.mm"

theorem paddss2
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


  assert |- ( ( K e. B /\ Y C_ A /\ Z C_ A ) -> ( X C_ Y -> ( Z .+ X ) C_ ( Z .+ Y ) ) )

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
    cZ
    cX
    c.pl
    co
    #
    cZ
    cY
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
    cZ
    wcel
    #
    @8
    cX
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
    #
    vr
    cX
    wrex
    #
    vq
    cZ
    wrex
    #
    wa
    #
    wo
    #
    @9
    @8
    cY
    wcel
    #
    wo
    #
    @12
    @15
    vr
    cY
    wrex
    #
    vq
    cZ
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
    @19
    @25
    wi
    @3
    @4
    @11
    @21
    @18
    @24
    @4
    @10
    @20
    @9
    cX
    cY
    @8
    ssel
    orim2d
    @4
    @17
    @23
    @12
    @4
    @16
    @22
    vq
    cZ
    @15
    vr
    cX
    cY
    ssrexv
    reximdv
    anim2d
    orim12d
    adantl
    @7
    @0
    @2
    cX
    cA
    wss
    #
    @26
    @19
    wb
    @0
    @1
    @2
    @4
    simpl1
    #
    @0
    @1
    @2
    @4
    simpl3
    #
    @4
    @3
    @28
    @4
    @0
    @1
    @28
    @2
    cX
    cY
    cA
    sstr
    3ad2antr2
    ancoms
    cA
    cB
    c.pl
    @8
    @13
    cK
    @14
    cZ
    cX
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
    @7
    @0
    @2
    @1
    @27
    @25
    wb
    @29
    @30
    @0
    @1
    @2
    @4
    simpl2
    cA
    cB
    c.pl
    @8
    @13
    cK
    @14
    cZ
    cY
    vr
    vq
    @31
    @32
    padd0.a
    padd0.p
    elpadd
    syl3anc
    3imtr4d
    ssrdv
    ex
end
