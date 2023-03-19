include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cltrr.mm"
include "wbr.mm"
include "c1st.mm"
include "cfv.mm"
include "c0r.mm"
include "cop.mm"
include "cltr.mm"
include "cnr.mm"
include "wceq.mm"
include "elreal2.mm"
include "simprbi.mm"
include "breqan12d.mm"
include "ltresr.mm"
include "syl6bb.mm"

theorem ltresr2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A <RR B <-> ( 1st ` A ) <R ( 1st ` B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cA
    cB
    cltrr
    wbr
    cA
    c1st
    cfv
    #
    c0r
    cop
    #
    cB
    c1st
    cfv
    #
    c0r
    cop
    #
    cltrr
    wbr
    @2
    @4
    cltr
    wbr
    @0
    @1
    cA
    @3
    cB
    @5
    cltrr
    @0
    @2
    cnr
    wcel
    cA
    @3
    wceq
    cA
    elreal2
    simprbi
    @1
    @4
    cnr
    wcel
    cB
    @5
    wceq
    cB
    elreal2
    simprbi
    breqan12d
    @2
    @4
    ltresr
    syl6bb
end
