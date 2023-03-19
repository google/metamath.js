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
include "lplnnleat.mm"
include "3expia.mm"
include "mt2d.mm"

theorem lplnneat
  let cA: class A
  let cP: class P
  let cK: class K
  let cX: class X
  assume lplnneat.a: |- A = ( Atoms ` K )
  assume lplnneat.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ X e. P ) -> -. X e. A )

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
    cA
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
    lplnneat.p
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
    cA
    cP
    cX
    cK
    @3
    cX
    @7
    lplnneat.a
    lplnneat.p
    lplnnleat
    3expia
    mt2d
end
