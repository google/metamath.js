include "crp.mm"
include "ccos.mm"
include "ccnv.mm"
include "c1.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "elin.mm"
include "cc.mm"
include "rpcn.mm"
include "biantrurd.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "cosf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mp2b.mm"
include "syl6rbbr.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem taupilem3
  let cA: class A


  assert |- ( A e. ( RR+ i^i ( `' cos " { 1 } ) ) <-> ( A e. RR+ /\ ( cos ` A ) = 1 ) )

  proof
    cA
    crp
    ccos
    ccnv
    c1
    csn
    cima
    #
    cin
    wcel
    cA
    crp
    wcel
    #
    cA
    @0
    wcel
    #
    wa
    @1
    cA
    ccos
    cfv
    c1
    wceq
    #
    wa
    cA
    crp
    @0
    elin
    @1
    @2
    @3
    @1
    @3
    cA
    cc
    wcel
    #
    @3
    wa
    #
    @2
    @1
    @4
    @3
    cA
    rpcn
    biantrurd
    cc
    cc
    ccos
    wf
    ccos
    cc
    wfn
    @2
    @5
    wb
    cosf
    cc
    cc
    ccos
    ffn
    cc
    c1
    cA
    ccos
    fniniseg
    mp2b
    syl6rbbr
    pm5.32i
    bitri
end
