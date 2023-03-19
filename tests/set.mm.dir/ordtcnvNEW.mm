include "cpreset.mm"
include "wcel.mm"
include "csn.mm"
include "cv.mm"
include "ccnv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "cordt.mm"
include "wb.mm"
include "vex.mm"
include "brcnv.mm"
include "a1i.mm"
include "notbid.mm"
include "rabbidv.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "uneq12d.mm"
include "uncom.mm"
include "syl6eq.mm"
include "uneq2d.mm"
include "fveq2d.mm"
include "codu.mm"
include "wceq.mm"
include "eqid.mm"
include "oduprs.mm"
include "odubas.mm"
include "cple.mm"
include "cxp.mm"
include "cin.mm"
include "cnveqi.mm"
include "cnvin.mm"
include "oduleval.mm"
include "cnvxp.mm"
include "ineq12i.mm"
include "3eqtri.mm"
include "ordtprsval.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem ordtcnvNEW
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let vx: setvar x
  let vy: setvar y
  assume ordtNEW.b: |- B = ( Base ` K )
  assume ordtNEW.l: |- .<_ = ( ( le ` K ) i^i ( B X. B ) )


  assert |- ( K e. Preset -> ( ordTop ` `' .<_ ) = ( ordTop ` .<_ ) )

  proof
    cK
    cpreset
    wcel
    #
    cB
    csn
    #
    vx
    cB
    vy
    cv
    #
    vx
    cv
    #
    c.le
    ccnv
    #
    wbr
    #
    wn
    #
    vy
    cB
    crab
    #
    cmpt
    #
    crn
    #
    vx
    cB
    @3
    @2
    @4
    wbr
    #
    wn
    #
    vy
    cB
    crab
    #
    cmpt
    #
    crn
    #
    cun
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    @1
    vx
    cB
    @2
    @3
    c.le
    wbr
    #
    wn
    #
    vy
    cB
    crab
    #
    cmpt
    #
    crn
    #
    vx
    cB
    @3
    @2
    c.le
    wbr
    #
    wn
    #
    vy
    cB
    crab
    #
    cmpt
    #
    crn
    #
    cun
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    @4
    cordt
    cfv
    #
    c.le
    cordt
    cfv
    @0
    @17
    @31
    ctg
    @0
    @16
    @30
    cfi
    @0
    @15
    @29
    @1
    @0
    @15
    @28
    @23
    cun
    @29
    @0
    @9
    @28
    @14
    @23
    @0
    @8
    @27
    @0
    vx
    cB
    @7
    @26
    @0
    @6
    @25
    vy
    cB
    @0
    @5
    @24
    @5
    @24
    wb
    @0
    @2
    @3
    c.le
    vy
    vex
    #
    vx
    vex
    #
    brcnv
    a1i
    notbid
    rabbidv
    mpteq2dv
    rneqd
    @0
    @13
    @22
    @0
    vx
    cB
    @12
    @21
    @0
    @11
    @20
    vy
    cB
    @0
    @10
    @19
    @10
    @19
    wb
    @0
    @3
    @2
    c.le
    @34
    @33
    brcnv
    a1i
    notbid
    rabbidv
    mpteq2dv
    rneqd
    uneq12d
    @28
    @23
    uncom
    syl6eq
    uneq2d
    fveq2d
    fveq2d
    @0
    cK
    codu
    cfv
    #
    cpreset
    wcel
    @32
    @18
    wceq
    @35
    cK
    @35
    eqid
    #
    oduprs
    vx
    vy
    cB
    @9
    @14
    @35
    @4
    cB
    @35
    cK
    @36
    ordtNEW.b
    odubas
    @4
    cK
    cple
    cfv
    #
    cB
    cB
    cxp
    #
    cin
    #
    ccnv
    @37
    ccnv
    #
    @38
    ccnv
    #
    cin
    @35
    cple
    cfv
    #
    @38
    cin
    c.le
    @39
    ordtNEW.l
    cnveqi
    @37
    @38
    cnvin
    @40
    @42
    @41
    @38
    @35
    @37
    cK
    @36
    @37
    eqid
    oduleval
    cB
    cB
    cnvxp
    ineq12i
    3eqtri
    @9
    eqid
    @14
    eqid
    ordtprsval
    syl
    vx
    vy
    cB
    @23
    @28
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    @23
    eqid
    @28
    eqid
    ordtprsval
    3eqtr4d
end
