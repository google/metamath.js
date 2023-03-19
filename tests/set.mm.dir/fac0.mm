include "cc0.mm"
include "c1.mm"
include "cn0.mm"
include "cmul.mm"
include "cid.mm"
include "cseq.mm"
include "cfa.mm"
include "c0ex.mm"
include "1ex.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cdif.mm"
include "cres.mm"
include "df-fac.mm"
include "cuz.mm"
include "cfv.mm"
include "cn.mm"
include "nnuz.mm"
include "dfn2.mm"
include "eqtr3i.mm"
include "reseq2i.mm"
include "cz.mm"
include "wcel.mm"
include "wfn.mm"
include "wceq.mm"
include "1z.mm"
include "seqfn.mm"
include "fnresdm.mm"
include "mp2b.mm"
include "uneq2i.mm"
include "eqtr4i.mm"
include "fvsnun1.mm"

theorem fac0



  assert |- ( ! ` 0 ) = 1

  proof
    cc0
    c1
    cn0
    cmul
    cid
    c1
    cseq
    #
    cfa
    c0ex
    1ex
    cfa
    cc0
    c1
    cop
    csn
    #
    @0
    cun
    @1
    @0
    cn0
    cc0
    csn
    cdif
    #
    cres
    #
    cun
    df-fac
    @3
    @0
    @1
    @0
    c1
    cuz
    cfv
    #
    cres
    #
    @3
    @0
    @4
    @2
    @0
    cn
    @4
    @2
    nnuz
    dfn2
    eqtr3i
    reseq2i
    c1
    cz
    wcel
    @0
    @4
    wfn
    @5
    @0
    wceq
    1z
    cmul
    cid
    c1
    seqfn
    @4
    @0
    fnresdm
    mp2b
    eqtr3i
    uneq2i
    eqtr4i
    fvsnun1
end
