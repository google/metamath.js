include "wpss.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "wn.mm"
include "pssss.mm"
include "sylan9ss.mm"
include "pssn2lp.mm"
include "psseq1.mm"
include "anbi1d.mm"
include "mtbiri.mm"
include "con2i.mm"
include "dfpss2.mm"
include "sylanbrc.mm"

theorem psstr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C. B /\ B C. C ) -> A C. C )

  proof
    cA
    cB
    wpss
    #
    cB
    cC
    wpss
    #
    wa
    #
    cA
    cC
    wss
    cA
    cC
    wceq
    #
    wn
    cA
    cC
    wpss
    @0
    @1
    cA
    cB
    cC
    cA
    cB
    pssss
    cB
    cC
    pssss
    sylan9ss
    @3
    @2
    @3
    @2
    cC
    cB
    wpss
    #
    @1
    wa
    cC
    cB
    pssn2lp
    @3
    @0
    @4
    @1
    cA
    cC
    cB
    psseq1
    anbi1d
    mtbiri
    con2i
    cA
    cC
    dfpss2
    sylanbrc
end
