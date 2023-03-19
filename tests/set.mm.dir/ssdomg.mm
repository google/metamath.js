include "wss.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "cid.mm"
include "cres.mm"
include "wf1.mm"
include "ssexg.mm"
include "simpr.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "wfo.mm"
include "wf1o.mm"
include "f1oi.mm"
include "dff1o3.mm"
include "mpbi.mm"
include "simpli.mm"
include "fof.mm"
include "ax-mp.mm"
include "fss.mm"
include "mpan.mm"
include "funi.mm"
include "cnvi.mm"
include "funeqi.mm"
include "mpbir.mm"
include "funres11.mm"
include "jctir.mm"
include "df-f1.mm"
include "sylibr.mm"
include "adantr.mm"
include "f1dom2g.mm"
include "syl3anc.mm"
include "expcom.mm"

theorem ssdomg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( B e. V -> ( A C_ B -> A ~<_ B ) )

  proof
    cA
    cB
    wss
    #
    cB
    cV
    wcel
    #
    cA
    cB
    cdom
    wbr
    #
    @0
    @1
    wa
    cA
    cvv
    wcel
    @1
    cA
    cB
    cid
    cA
    cres
    #
    wf1
    #
    @2
    cA
    cB
    cV
    ssexg
    @0
    @1
    simpr
    @0
    @4
    @1
    @0
    cA
    cB
    @3
    wf
    #
    @3
    ccnv
    wfun
    #
    wa
    @4
    @0
    @5
    @6
    cA
    cA
    @3
    wf
    #
    @0
    @5
    cA
    cA
    @3
    wfo
    #
    @7
    @8
    @6
    cA
    cA
    @3
    wf1o
    @8
    @6
    wa
    cA
    f1oi
    cA
    cA
    @3
    dff1o3
    mpbi
    simpli
    cA
    cA
    @3
    fof
    ax-mp
    cA
    cA
    cB
    @3
    fss
    mpan
    cid
    ccnv
    #
    wfun
    #
    @6
    @10
    cid
    wfun
    funi
    @9
    cid
    cnvi
    funeqi
    mpbir
    cA
    cid
    funres11
    ax-mp
    jctir
    cA
    cB
    @3
    df-f1
    sylibr
    adantr
    cA
    cB
    @3
    cvv
    cV
    f1dom2g
    syl3anc
    expcom
end
