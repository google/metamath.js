include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wbr.mm"
include "disj1.mm"
include "wb.mm"
include "cvv.mm"
include "elecg.mm"
include "el2v1.mm"
include "adantr.mm"
include "elecALTV.mm"
include "el2v2.mm"
include "adantl.mm"
include "notbid.mm"
include "imbi12d.mm"
include "albidv.mm"
include "syl5bb.mm"

theorem ecin0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint V x
  disjoint W x
  assert |- ( ( A e. V /\ B e. W ) -> ( ( [ A ] R i^i [ B ] R ) = (/) <-> A. x ( A R x -> -. B R x ) ) )

  proof
    cA
    cR
    cec
    #
    cB
    cR
    cec
    #
    cin
    c0
    wceq
    vx
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wn
    #
    wi
    #
    vx
    wal
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    @2
    cR
    wbr
    #
    cB
    @2
    cR
    wbr
    #
    wn
    #
    wi
    #
    vx
    wal
    vx
    @0
    @1
    disj1
    @9
    @6
    @13
    vx
    @9
    @3
    @10
    @5
    @12
    @7
    @3
    @10
    wb
    #
    @8
    @7
    @14
    vx
    @2
    cA
    cR
    cvv
    cV
    elecg
    el2v1
    adantr
    @9
    @4
    @11
    @8
    @4
    @11
    wb
    #
    @7
    @8
    @15
    vx
    cB
    @2
    cR
    cW
    cvv
    elecALTV
    el2v2
    adantl
    notbid
    imbi12d
    albidv
    syl5bb
end
