include "cword.mm"
include "wcel.mm"
include "ccnv.mm"
include "wfun.mm"
include "cz.mm"
include "w3a.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "wf1.mm"
include "wa.mm"
include "wf.mm"
include "wrdf.mm"
include "df-f1.mm"
include "biimpri.mm"
include "sylan.mm"
include "3adant3.mm"
include "adantr.mm"
include "simpl3.mm"
include "simpr.mm"
include "cshf1.mm"
include "syl3anc.mm"
include "ex.mm"
include "simprbi.mm"
include "syl6.mm"

theorem cshinj
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G


  assert |- ( ( F e. Word A /\ Fun `' F /\ S e. ZZ ) -> ( G = ( F cyclShift S ) -> Fun `' G ) )

  proof
    cF
    cA
    cword
    wcel
    #
    cF
    ccnv
    wfun
    #
    cS
    cz
    wcel
    #
    w3a
    #
    cG
    cF
    cS
    ccsh
    co
    wceq
    #
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    cA
    cG
    wf1
    #
    cG
    ccnv
    wfun
    #
    @3
    @4
    @6
    @3
    @4
    wa
    @5
    cA
    cF
    wf1
    #
    @2
    @4
    @6
    @3
    @8
    @4
    @0
    @1
    @8
    @2
    @0
    @5
    cA
    cF
    wf
    #
    @1
    @8
    cA
    cF
    wrdf
    @8
    @9
    @1
    wa
    @5
    cA
    cF
    df-f1
    biimpri
    sylan
    3adant3
    adantr
    @0
    @1
    @2
    @4
    simpl3
    @3
    @4
    simpr
    cA
    cS
    cF
    cG
    cshf1
    syl3anc
    ex
    @6
    @5
    cA
    cG
    wf
    @7
    @5
    cA
    cG
    df-f1
    simprbi
    syl6
end
