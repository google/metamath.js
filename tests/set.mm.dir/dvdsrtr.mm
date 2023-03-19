include "crg.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "dvdsr.mm"
include "anbi12i.mm"
include "an4.mm"
include "bitri.mm"
include "reeanv.mm"
include "simplrl.mm"
include "simpll.mm"
include "simprr.mm"
include "simprl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "dvdsrmul.mm"
include "syl2anc.mm"
include "ringass.mm"
include "syl13anc.mm"
include "breqtrd.mm"
include "oveq2.mm"
include "id.mm"
include "sylan9eq.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "3impib.mm"

theorem dvdsrtr
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vz: setvar z
  let c.x: class .x.
  assume dvdsr.1: |- B = ( Base ` R )
  assume dvdsr.2: |- .|| = ( ||r ` R )


  assert |- ( ( R e. Ring /\ Y .|| Z /\ Z .|| X ) -> Y .|| X )

  proof
    cR
    crg
    wcel
    #
    cY
    cZ
    c.pa
    wbr
    #
    cZ
    cX
    c.pa
    wbr
    #
    cY
    cX
    c.pa
    wbr
    #
    @1
    @2
    wa
    #
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    wa
    #
    vy
    cv
    #
    cY
    cR
    cmulr
    cfv
    #
    co
    #
    cZ
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cv
    #
    cZ
    @9
    co
    #
    cX
    wceq
    #
    vx
    cB
    wrex
    #
    wa
    #
    wa
    #
    @0
    @3
    @4
    @5
    @12
    wa
    #
    @6
    @16
    wa
    #
    wa
    @18
    @1
    @19
    @2
    @20
    vy
    cB
    c.pa
    cR
    @9
    cY
    cZ
    dvdsr.1
    dvdsr.2
    @9
    eqid
    #
    dvdsr
    vx
    cB
    c.pa
    cR
    @9
    cZ
    cX
    dvdsr.1
    dvdsr.2
    @21
    dvdsr
    anbi12i
    @5
    @12
    @6
    @16
    an4
    bitri
    @0
    @7
    @17
    @3
    @17
    @11
    @15
    wa
    #
    vx
    cB
    wrex
    vy
    cB
    wrex
    @0
    @7
    wa
    #
    @3
    @11
    @15
    vy
    vx
    cB
    cB
    reeanv
    @23
    @22
    @3
    vy
    vx
    cB
    cB
    @23
    @8
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    wa
    #
    wa
    #
    cY
    @13
    @10
    @9
    co
    #
    c.pa
    wbr
    @22
    @3
    @27
    cY
    @13
    @8
    @9
    co
    #
    cY
    @9
    co
    #
    @28
    c.pa
    @27
    @5
    @29
    cB
    wcel
    #
    cY
    @30
    c.pa
    wbr
    @0
    @5
    @6
    @26
    simplrl
    #
    @27
    @0
    @25
    @24
    @31
    @0
    @7
    @26
    simpll
    #
    @23
    @24
    @25
    simprr
    #
    @23
    @24
    @25
    simprl
    #
    cB
    cR
    @9
    @13
    @8
    dvdsr.1
    @21
    ringcl
    syl3anc
    cB
    c.pa
    cR
    @9
    cY
    @29
    dvdsr.1
    dvdsr.2
    @21
    dvdsrmul
    syl2anc
    @27
    @0
    @25
    @24
    @5
    @30
    @28
    wceq
    @33
    @34
    @35
    @32
    cB
    cR
    @9
    @13
    @8
    cY
    dvdsr.1
    @21
    ringass
    syl13anc
    breqtrd
    @22
    @28
    cX
    cY
    c.pa
    @11
    @15
    @28
    @14
    cX
    @10
    cZ
    @13
    @9
    oveq2
    @15
    id
    sylan9eq
    breq2d
    syl5ibcom
    rexlimdvva
    syl5bir
    expimpd
    syl5bi
    3impib
end
