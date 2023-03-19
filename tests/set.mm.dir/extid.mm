include "cid.mm"
include "ccnv.mm"
include "cec.mm"
include "wceq.mm"
include "csn.mm"
include "wcel.mm"
include "cnvi.mm"
include "eceq2i.mm"
include "ecidsn.mm"
include "eqtri.mm"
include "eqeq12i.mm"
include "sneqbg.mm"
include "syl5bb.mm"

theorem extid
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( [ A ] `' _I = [ B ] `' _I <-> A = B ) )

  proof
    cA
    cid
    ccnv
    #
    cec
    #
    cB
    @0
    cec
    #
    wceq
    cA
    csn
    #
    cB
    csn
    #
    wceq
    cA
    cV
    wcel
    cA
    cB
    wceq
    @1
    @3
    @2
    @4
    @1
    cA
    cid
    cec
    @3
    @0
    cid
    cA
    cnvi
    eceq2i
    cA
    ecidsn
    eqtri
    @2
    cB
    cid
    cec
    @4
    @0
    cid
    cB
    cnvi
    eceq2i
    cB
    ecidsn
    eqtri
    eqeq12i
    cA
    cB
    cV
    sneqbg
    syl5bb
end
