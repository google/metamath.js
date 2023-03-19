include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "cdib.mm"
include "eqid.mm"
include "dihvalb.mm"
include "diblss.mm"
include "eqeltrd.mm"
include "anassrs.mm"
include "wn.mm"
include "catm.mm"
include "cdic.mm"
include "clsm.mm"
include "cjn.mm"
include "cmee.mm"
include "dihlsscpre.mm"
include "pm2.61dan.mm"

theorem dihlss
  let cB: class B
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  assume dihlss.b: |- B = ( Base ` K )
  assume dihlss.h: |- H = ( LHyp ` K )
  assume dihlss.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihlss.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihlss.s: |- S = ( LSubSp ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B ) -> ( I ` X ) e. S )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cB
    wcel
    #
    wa
    cX
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    cX
    cI
    cfv
    #
    cS
    wcel
    #
    @0
    @1
    @3
    @5
    @0
    @1
    @3
    wa
    wa
    @4
    cX
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    cS
    cB
    @6
    cH
    cI
    cK
    @2
    chlt
    cW
    cX
    dihlss.b
    @2
    eqid
    #
    dihlss.h
    dihlss.i
    @6
    eqid
    #
    dihvalb
    cB
    cS
    cU
    cH
    @6
    cK
    @2
    cW
    cX
    dihlss.b
    @7
    dihlss.h
    dihlss.u
    @8
    dihlss.s
    diblss
    eqeltrd
    anassrs
    @0
    @1
    @3
    wn
    @5
    cK
    catm
    cfv
    #
    cB
    cW
    cK
    cdic
    cfv
    cfv
    #
    @6
    cU
    clsm
    cfv
    #
    cS
    cU
    cH
    cI
    cK
    cjn
    cfv
    #
    cK
    @2
    cK
    cmee
    cfv
    #
    cW
    cX
    dihlss.b
    @7
    @12
    eqid
    @13
    eqid
    @9
    eqid
    dihlss.h
    dihlss.i
    @8
    @10
    eqid
    dihlss.u
    dihlss.s
    @11
    eqid
    dihlsscpre
    anassrs
    pm2.61dan
end
