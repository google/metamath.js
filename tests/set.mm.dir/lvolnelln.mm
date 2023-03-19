include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "clat.mm"
include "cbs.mm"
include "hllat.mm"
include "eqid.mm"
include "lvolbase.mm"
include "latref.mm"
include "syl2an.mm"
include "wn.mm"
include "lvolnlelln.mm"
include "3expia.mm"
include "mt2d.mm"

theorem lvolnelln
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  assume lvolnelln.l: |- N = ( LLines ` K )
  assume lvolnelln.v: |- V = ( LVols ` K )


  assert |- ( ( K e. HL /\ X e. V ) -> -. X e. N )

  proof
    cK
    chlt
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    cX
    cN
    wcel
    #
    cX
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    @0
    cK
    clat
    wcel
    cX
    cK
    cbs
    cfv
    #
    wcel
    @4
    @1
    cK
    hllat
    @5
    cK
    cV
    cX
    @5
    eqid
    #
    lvolnelln.v
    lvolbase
    @5
    cK
    @3
    cX
    @6
    @3
    eqid
    #
    latref
    syl2an
    @0
    @1
    @2
    @4
    wn
    cK
    @3
    cN
    cV
    cX
    cX
    @7
    lvolnelln.l
    lvolnelln.v
    lvolnlelln
    3expia
    mt2d
end
