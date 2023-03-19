include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cop.mm"
include "wceq.mm"
include "wb.mm"
include "fsng.mm"
include "3adant3.mm"
include "mpbiri.mm"
include "wss.mm"
include "snssi.mm"
include "3ad2ant2.mm"
include "fssd.mm"
include "cvv.mm"
include "simp3.mm"
include "snex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "mpbird.mm"

theorem mapsnop
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume mapsnop.f: |- F = { <. X , Y >. }


  assert |- ( ( X e. V /\ Y e. R /\ R e. W ) -> F e. ( R ^m { X } ) )

  proof
    cX
    cV
    wcel
    #
    cY
    cR
    wcel
    #
    cR
    cW
    wcel
    #
    w3a
    #
    cF
    cR
    cX
    csn
    #
    cmap
    co
    wcel
    #
    @4
    cR
    cF
    wf
    #
    @3
    @4
    cY
    csn
    #
    cR
    cF
    @3
    @4
    @7
    cF
    wf
    #
    cF
    cX
    cY
    cop
    csn
    wceq
    #
    mapsnop.f
    @0
    @1
    @8
    @9
    wb
    @2
    cX
    cY
    cV
    cR
    cF
    fsng
    3adant3
    mpbiri
    @1
    @0
    @7
    cR
    wss
    @2
    cY
    cR
    snssi
    3ad2ant2
    fssd
    @3
    @2
    @4
    cvv
    wcel
    @5
    @6
    wb
    @0
    @1
    @2
    simp3
    cX
    snex
    cR
    @4
    cF
    cW
    cvv
    elmapg
    sylancl
    mpbird
end
