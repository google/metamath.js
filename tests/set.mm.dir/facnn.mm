include "cfa.mm"
include "cfv.mm"
include "cmul.mm"
include "cid.mm"
include "c1.mm"
include "cseq.mm"
include "wceq.mm"
include "cn0.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cn.mm"
include "c0ex.mm"
include "1ex.mm"
include "cop.mm"
include "cun.mm"
include "cres.mm"
include "df-fac.mm"
include "cuz.mm"
include "nnuz.mm"
include "dfn2.mm"
include "eqtr3i.mm"
include "reseq2i.mm"
include "cz.mm"
include "wcel.mm"
include "wfn.mm"
include "1z.mm"
include "seqfn.mm"
include "fnresdm.mm"
include "mp2b.mm"
include "uneq2i.mm"
include "eqtr4i.mm"
include "fvsnun2.mm"
include "eleq2s.mm"

theorem facnn
  let cN: class N


  assert |- ( N e. NN -> ( ! ` N ) = ( seq 1 ( x. , _I ) ` N ) )

  proof
    cN
    cfa
    cfv
    cN
    cmul
    cid
    c1
    cseq
    #
    cfv
    wceq
    cN
    cn0
    cc0
    csn
    cdif
    #
    cn
    cc0
    c1
    cn0
    cN
    @0
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
    @2
    @0
    @1
    cres
    #
    cun
    df-fac
    @3
    @0
    @2
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
    @1
    @0
    cn
    @4
    @1
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
    fvsnun2
    dfn2
    eleq2s
end
