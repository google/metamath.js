include "wcel.mm"
include "wa.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "ecin0.mm"
include "necon3abid.mm"
include "notnotb.mm"
include "anbi2i.mm"
include "exbii.mm"
include "exanali.mm"
include "bitri.mm"
include "syl6bbr.mm"

theorem ecinn0
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
  assert |- ( ( A e. V /\ B e. W ) -> ( ( [ A ] R i^i [ B ] R ) =/= (/) <-> E. x ( A R x /\ B R x ) ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cA
    cR
    cec
    cB
    cR
    cec
    cin
    #
    c0
    wne
    cA
    vx
    cv
    #
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
    vx
    wal
    #
    wn
    #
    @3
    @4
    wa
    #
    vx
    wex
    #
    @0
    @6
    @1
    c0
    vx
    cA
    cB
    cR
    cV
    cW
    ecin0
    necon3abid
    @9
    @3
    @5
    wn
    #
    wa
    #
    vx
    wex
    @7
    @8
    @11
    vx
    @4
    @10
    @3
    @4
    notnotb
    anbi2i
    exbii
    @3
    @5
    vx
    exanali
    bitri
    syl6bbr
end
