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
include "llnbase.mm"
include "latref.mm"
include "syl2an.mm"
include "wn.mm"
include "llnnleat.mm"
include "3expia.mm"
include "mt2d.mm"

theorem llnneat
  let cA: class A
  let cK: class K
  let cN: class N
  let cX: class X
  assume llnneat.a: |- A = ( Atoms ` K )
  assume llnneat.n: |- N = ( LLines ` K )


  assert |- ( ( K e. HL /\ X e. N ) -> -. X e. A )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
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
    cK
    cN
    cX
    @5
    eqid
    #
    llnneat.n
    llnbase
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
    cX
    cK
    @3
    cN
    cX
    @7
    llnneat.a
    llnneat.n
    llnnleat
    3expia
    mt2d
end
