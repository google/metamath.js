include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "wfun.mm"
include "ctp.mm"
include "wa.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "funpr.mm"
include "funsn.mm"
include "jctir.mm"
include "dmprop.mm"
include "df-pr.mm"
include "eqtri.mm"
include "dmsnop.mm"
include "ineq12i.mm"
include "disjsn2.mm"
include "anim12i.mm"
include "undisj1.mm"
include "sylib.mm"
include "syl5eq.mm"
include "funun.mm"
include "syl2an.mm"
include "3impb.mm"
include "df-tp.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem funtp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume funtp.1: |- A e. _V
  assume funtp.2: |- B e. _V
  assume funtp.3: |- C e. _V
  assume funtp.4: |- D e. _V
  assume funtp.5: |- E e. _V
  assume funtp.6: |- F e. _V


  assert |- ( ( A =/= B /\ A =/= C /\ B =/= C ) -> Fun { <. A , D >. , <. B , E >. , <. C , F >. } )

  proof
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    w3a
    cA
    cD
    cop
    #
    cB
    cE
    cop
    #
    cpr
    #
    cC
    cF
    cop
    #
    csn
    #
    cun
    #
    wfun
    #
    @3
    @4
    @6
    ctp
    #
    wfun
    @0
    @1
    @2
    @9
    @0
    @5
    wfun
    #
    @7
    wfun
    #
    wa
    @5
    cdm
    #
    @7
    cdm
    #
    cin
    #
    c0
    wceq
    @9
    @1
    @2
    wa
    #
    @0
    @11
    @12
    cA
    cB
    cD
    cE
    funtp.1
    funtp.2
    funtp.4
    funtp.5
    funpr
    cC
    cF
    funtp.3
    funtp.6
    funsn
    jctir
    @16
    @15
    cA
    csn
    #
    cB
    csn
    #
    cun
    #
    cC
    csn
    #
    cin
    #
    c0
    @13
    @19
    @14
    @20
    @13
    cA
    cB
    cpr
    @19
    cA
    cD
    cB
    cE
    funtp.4
    funtp.5
    dmprop
    cA
    cB
    df-pr
    eqtri
    cC
    cF
    funtp.6
    dmsnop
    ineq12i
    @16
    @17
    @20
    cin
    c0
    wceq
    #
    @18
    @20
    cin
    c0
    wceq
    #
    wa
    @21
    c0
    wceq
    @1
    @22
    @2
    @23
    cA
    cC
    disjsn2
    cB
    cC
    disjsn2
    anim12i
    @17
    @18
    @20
    undisj1
    sylib
    syl5eq
    @5
    @7
    funun
    syl2an
    3impb
    @10
    @8
    @3
    @4
    @6
    df-tp
    funeqi
    sylibr
end
