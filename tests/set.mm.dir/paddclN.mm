include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "catm.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cjn.mm"
include "cple.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "simp1.mm"
include "eqid.mm"
include "psubssat.mm"
include "3adant3.mm"
include "3adant2.mm"
include "paddssat.mm"
include "syl3anc.mm"
include "wa.mm"
include "wo.mm"
include "olc.mm"
include "wb.mm"
include "elpadd.mm"
include "wceq.mm"
include "padd4N.mm"
include "syl122anc.mm"
include "paddidm.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "bitr3d.mm"
include "syl5ib.mm"
include "expd.mm"
include "ralrimiv.mm"
include "ispsubsp2.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"

theorem paddclN
  let c.pl: class .+
  let cS: class S
  let cK: class K
  let cX: class X
  let cY: class Y
  let cB: class B
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume paddidm.s: |- S = ( PSubSp ` K )
  assume paddidm.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. HL /\ X e. S /\ Y e. S ) -> ( X .+ Y ) e. S )

  proof
    cK
    chlt
    wcel
    #
    cX
    cS
    wcel
    #
    cY
    cS
    wcel
    #
    w3a
    #
    cX
    cY
    c.pl
    co
    #
    cS
    wcel
    #
    @4
    cK
    catm
    cfv
    #
    wss
    #
    vp
    cv
    #
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
    @4
    wrex
    vq
    @4
    wrex
    #
    @8
    @4
    wcel
    #
    wi
    #
    vp
    @6
    wral
    #
    @3
    @0
    cX
    @6
    wss
    #
    cY
    @6
    wss
    #
    @7
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @15
    @2
    @6
    chlt
    cS
    cK
    cX
    @6
    eqid
    #
    paddidm.s
    psubssat
    3adant3
    #
    @0
    @2
    @16
    @1
    @6
    chlt
    cS
    cK
    cY
    @18
    paddidm.s
    psubssat
    3adant2
    #
    @6
    chlt
    c.pl
    cK
    cX
    cY
    @18
    paddidm.p
    paddssat
    syl3anc
    #
    @3
    @13
    vp
    @6
    @3
    @8
    @6
    wcel
    #
    @11
    @12
    @22
    @11
    wa
    #
    @12
    @12
    wo
    #
    @23
    wo
    #
    @3
    @12
    @23
    @24
    olc
    @3
    @8
    @4
    @4
    c.pl
    co
    #
    wcel
    #
    @25
    @12
    @3
    @0
    @7
    @7
    @27
    @25
    wb
    @17
    @21
    @21
    @6
    chlt
    c.pl
    @8
    @9
    cK
    @10
    @4
    @4
    vr
    vq
    @10
    eqid
    #
    @9
    eqid
    #
    @18
    paddidm.p
    elpadd
    syl3anc
    @3
    @26
    @4
    @8
    @3
    @26
    cX
    cX
    c.pl
    co
    #
    cY
    cY
    c.pl
    co
    #
    c.pl
    co
    #
    @4
    @3
    @0
    @15
    @16
    @15
    @16
    @26
    @32
    wceq
    @17
    @19
    @20
    @19
    @20
    @6
    c.pl
    cK
    cY
    cX
    cY
    cX
    @18
    paddidm.p
    padd4N
    syl122anc
    @3
    @30
    cX
    @31
    cY
    c.pl
    @0
    @1
    @30
    cX
    wceq
    @2
    chlt
    c.pl
    cS
    cK
    cX
    paddidm.s
    paddidm.p
    paddidm
    3adant3
    @0
    @2
    @31
    cY
    wceq
    @1
    chlt
    c.pl
    cS
    cK
    cY
    paddidm.s
    paddidm.p
    paddidm
    3adant2
    oveq12d
    eqtrd
    eleq2d
    bitr3d
    syl5ib
    expd
    ralrimiv
    @0
    @1
    @5
    @7
    @14
    wa
    wb
    @2
    @6
    chlt
    cS
    @9
    cK
    @10
    @4
    vr
    vq
    vp
    @28
    @29
    @18
    paddidm.s
    ispsubsp2
    3ad2ant1
    mpbir2and
end
