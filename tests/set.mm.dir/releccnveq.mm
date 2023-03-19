include "ccnv.mm"
include "cec.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wrel.mm"
include "wa.mm"
include "wbr.mm"
include "dfcleq.mm"
include "releleccnv.mm"
include "bi2bian9.mm"
include "albidv.mm"
include "syl5bb.mm"

theorem releccnveq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint S x
  assert |- ( ( Rel R /\ Rel S ) -> ( [ A ] `' R = [ B ] `' S <-> A. x ( x R A <-> x S B ) ) )

  proof
    cA
    cR
    ccnv
    cec
    #
    cB
    cS
    ccnv
    cec
    #
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
    wb
    #
    vx
    wal
    cR
    wrel
    #
    cS
    wrel
    #
    wa
    #
    @2
    cA
    cR
    wbr
    #
    @2
    cB
    cS
    wbr
    #
    wb
    #
    vx
    wal
    vx
    @0
    @1
    dfcleq
    @8
    @5
    @11
    vx
    @6
    @3
    @9
    @7
    @4
    @10
    @2
    cA
    cR
    releleccnv
    @2
    cB
    cS
    releleccnv
    bi2bian9
    albidv
    syl5bb
end
