include "chash.mm"
include "cvv.mm"
include "cin.mm"
include "cres.mm"
include "wfn.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "hashf.mm"
include "ffn.mm"
include "fnresin2.mm"
include "mp2b.mm"
include "wceq.mm"
include "wb.mm"
include "inv1.mm"
include "reseq2i.mm"
include "fneq12.mm"
include "mp2an.mm"
include "mpbi.mm"

theorem hashresfn
  let cA: class A


  assert |- ( # |` A ) Fn A

  proof
    chash
    cA
    cvv
    cin
    #
    cres
    #
    @0
    wfn
    #
    chash
    cA
    cres
    #
    cA
    wfn
    #
    cvv
    cn0
    cpnf
    csn
    cun
    #
    chash
    wf
    chash
    cvv
    wfn
    @2
    hashf
    cvv
    @5
    chash
    ffn
    cvv
    cA
    chash
    fnresin2
    mp2b
    @1
    @3
    wceq
    @0
    cA
    wceq
    @2
    @4
    wb
    @0
    cA
    chash
    cA
    inv1
    #
    reseq2i
    @6
    @0
    cA
    @1
    @3
    fneq12
    mp2an
    mpbi
end
