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
include "lplnbase.mm"
include "latref.mm"
include "syl2an.mm"
include "wn.mm"
include "lplnnlelln.mm"
include "3expia.mm"
include "mt2d.mm"

theorem lplnnelln
  let cP: class P
  let cK: class K
  let cN: class N
  let cX: class X
  assume lplnnelln.n: |- N = ( LLines ` K )
  assume lplnnelln.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ X e. P ) -> -. X e. N )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
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
    cP
    cK
    cX
    @5
    eqid
    #
    lplnnelln.p
    lplnbase
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
    cP
    cK
    @3
    cN
    cX
    cX
    @7
    lplnnelln.n
    lplnnelln.p
    lplnnlelln
    3expia
    mt2d
end
