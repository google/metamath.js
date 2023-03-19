include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "ccom.mm"
include "cfv.mm"
include "co.mm"
include "catm.mm"
include "wrex.mm"
include "eqid.mm"
include "lhpexnle.mm"
include "3ad2ant1.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "cmee.mm"
include "trlcolem.mm"
include "syl121anc.mm"
include "rexlimddv.mm"

theorem trlco
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vp: setvar p
  assume trlco.l: |- .<_ = ( le ` K )
  assume trlco.j: |- .\/ = ( join ` K )
  assume trlco.h: |- H = ( LHyp ` K )
  assume trlco.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlco.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) -> ( R ` ( F o. G ) ) .<_ ( ( R ` F ) .\/ ( R ` G ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    cF
    cG
    ccom
    cR
    cfv
    cF
    cR
    cfv
    cG
    cR
    cfv
    c.or
    co
    c.le
    wbr
    #
    vp
    cK
    catm
    cfv
    #
    @0
    @1
    @5
    vp
    @7
    wrex
    @2
    @7
    cH
    cK
    c.le
    cW
    vp
    trlco.l
    @7
    eqid
    #
    trlco.h
    lhpexnle
    3ad2ant1
    @3
    @4
    @7
    wcel
    @5
    wa
    #
    wa
    @0
    @1
    @2
    @9
    @6
    @0
    @1
    @2
    @9
    simpl1
    @0
    @1
    @2
    @9
    simpl2
    @0
    @1
    @2
    @9
    simpl3
    @3
    @9
    simpr
    @7
    @4
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cK
    cmee
    cfv
    #
    cW
    trlco.l
    trlco.j
    trlco.h
    trlco.t
    trlco.r
    @10
    eqid
    @8
    trlcolem
    syl121anc
    rexlimddv
end
