include "crp.mm"
include "csin.mm"
include "ccnv.mm"
include "cc0.mm"
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
include "sinf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mp2b.mm"
include "syl6rbbr.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem pilem1
  let cA: class A


  assert |- ( A e. ( RR+ i^i ( `' sin " { 0 } ) ) <-> ( A e. RR+ /\ ( sin ` A ) = 0 ) )

  proof
    cA
    crp
    csin
    ccnv
    cc0
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
    csin
    cfv
    cc0
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
    csin
    wf
    csin
    cc
    wfn
    @2
    @5
    wb
    sinf
    cc
    cc
    csin
    ffn
    cc
    cc0
    cA
    csin
    fniniseg
    mp2b
    syl6rbbr
    pm5.32i
    bitri
end
