include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cs1.mm"
include "wrex.mm"
include "cc0.mm"
include "cwwlksn.mm"
include "co.mm"
include "wrdl1exs1.mm"
include "crab.mm"
include "wwlksn0s.mm"
include "eleq2i.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "bitri.mm"
include "rexeqi.mm"
include "3imtr4i.mm"

theorem wwlksn0
  let vv: setvar v
  let cG: class G
  let cV: class V
  let cW: class W
  let vw: setvar w
  assume wwlkssswrd.v: |- V = ( Vtx ` G )

  disjoint G v
  disjoint V v
  disjoint W v
  disjoint G w
  disjoint V w
  disjoint W w
  assert |- ( W e. ( 0 WWalksN G ) -> E. v e. V W = <" v "> )

  proof
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    cW
    chash
    cfv
    #
    c1
    wceq
    #
    wa
    #
    cW
    vv
    cv
    cs1
    wceq
    #
    vv
    @0
    wrex
    cW
    cc0
    cG
    cwwlksn
    co
    #
    wcel
    #
    @5
    vv
    cV
    wrex
    @0
    cW
    vv
    wrdl1exs1
    @7
    cW
    vw
    cv
    #
    chash
    cfv
    #
    c1
    wceq
    #
    vw
    @1
    crab
    #
    wcel
    @4
    @6
    @11
    cW
    vw
    cG
    wwlksn0s
    eleq2i
    @10
    @3
    vw
    cW
    @1
    @8
    cW
    wceq
    @9
    @2
    c1
    @8
    cW
    chash
    fveq2
    eqeq1d
    elrab
    bitri
    @5
    vv
    cV
    @0
    wwlkssswrd.v
    rexeqi
    3imtr4i
end
