include "wcel.mm"
include "wa.mm"
include "ccoss.mm"
include "wbr.mm"
include "ccnv.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "brcoss3.mm"
include "cnvcosseq.mm"
include "eceq2i.mm"
include "ineq12i.mm"
include "neeq1i.mm"
include "syl6bb.mm"

theorem br2coss
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A ,~ ,~ R B <-> ( [ A ] ,~ R i^i [ B ] ,~ R ) =/= (/) ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cA
    cB
    cR
    ccoss
    #
    ccoss
    wbr
    cA
    @0
    ccnv
    #
    cec
    #
    cB
    @1
    cec
    #
    cin
    #
    c0
    wne
    cA
    @0
    cec
    #
    cB
    @0
    cec
    #
    cin
    #
    c0
    wne
    cA
    cB
    @0
    cV
    cW
    brcoss3
    @4
    @7
    c0
    @2
    @5
    @3
    @6
    @1
    @0
    cA
    cR
    cnvcosseq
    #
    eceq2i
    @1
    @0
    cB
    @8
    eceq2i
    ineq12i
    neeq1i
    syl6bb
end
