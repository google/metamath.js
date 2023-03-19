include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cssr.mm"
include "wbr.mm"
include "wb.mm"
include "wal.mm"
include "wss.mm"
include "ccnv.mm"
include "cec.mm"
include "wceq.mm"
include "brssr.mm"
include "bi2bian9.mm"
include "albidv.mm"
include "wrel.mm"
include "relssr.mm"
include "releccnveq.mm"
include "mp2an.mm"
include "ssext.mm"
include "3bitr4g.mm"

theorem extssr
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x


  assert |- ( ( A e. V /\ B e. W ) -> ( [ A ] `' _S = [ B ] `' _S <-> A = B ) )

  proof
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
    vx
    cv
    #
    cA
    cssr
    wbr
    #
    @3
    cB
    cssr
    wbr
    #
    wb
    #
    vx
    wal
    #
    @3
    cA
    wss
    #
    @3
    cB
    wss
    #
    wb
    #
    vx
    wal
    cA
    cssr
    ccnv
    #
    cec
    cB
    @11
    cec
    wceq
    #
    cA
    cB
    wceq
    @2
    @6
    @10
    vx
    @0
    @4
    @8
    @1
    @5
    @9
    @3
    cA
    cV
    brssr
    @3
    cB
    cW
    brssr
    bi2bian9
    albidv
    cssr
    wrel
    #
    @13
    @12
    @7
    wb
    relssr
    relssr
    vx
    cA
    cB
    cssr
    cssr
    releccnveq
    mp2an
    vx
    cA
    cB
    ssext
    3bitr4g
end
