include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cop.mm"
include "wf1.mm"
include "wss.mm"
include "wf1o.mm"
include "f1osng.mm"
include "f1of1.mm"
include "syl.mm"
include "snssi.mm"
include "adantl.mm"
include "f1ss.mm"
include "syl2anc.mm"

theorem f1sng
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. V /\ B e. W ) -> { <. A , B >. } : { A } -1-1-> W )

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
    cA
    csn
    #
    cB
    csn
    #
    cA
    cB
    cop
    csn
    #
    wf1
    #
    @4
    cW
    wss
    #
    @3
    cW
    @5
    wf1
    @2
    @3
    @4
    @5
    wf1o
    @6
    cA
    cB
    cV
    cW
    f1osng
    @3
    @4
    @5
    f1of1
    syl
    @1
    @7
    @0
    cB
    cW
    snssi
    adantl
    @3
    @4
    cW
    @5
    f1ss
    syl2anc
end
