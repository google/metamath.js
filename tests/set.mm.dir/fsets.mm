include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "wss.mm"
include "difss.mm"
include "fssres.mm"
include "mpan2.mm"
include "cin.mm"
include "resres.mm"
include "invdif.mm"
include "reseq2i.mm"
include "eqtri.mm"
include "wfn.mm"
include "wceq.mm"
include "ffn.mm"
include "fnresdm.mm"
include "syl.mm"
include "reseq1d.mm"
include "syl5reqr.mm"
include "feq1d.mm"
include "mpbird.mm"
include "adantl.mm"
include "fsnunf2.mm"
include "syl3an1.mm"
include "wb.mm"
include "simp1l.mm"
include "simp3.mm"
include "setsval.mm"
include "syl2anc.mm"

theorem fsets
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( ( F e. V /\ F : A --> B ) /\ X e. A /\ Y e. B ) -> ( F sSet <. X , Y >. ) : A --> B )

  proof
    cF
    cV
    wcel
    #
    cA
    cB
    cF
    wf
    #
    wa
    #
    cX
    cA
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cA
    cB
    cF
    cX
    cY
    cop
    #
    csts
    co
    #
    wf
    #
    cA
    cB
    cF
    cvv
    cX
    csn
    #
    cdif
    #
    cres
    #
    @6
    csn
    cun
    #
    wf
    #
    @2
    cA
    @9
    cdif
    #
    cB
    @11
    wf
    #
    @3
    @4
    @13
    @1
    @15
    @0
    @1
    @15
    @14
    cB
    cF
    @14
    cres
    #
    wf
    #
    @1
    @14
    cA
    wss
    @17
    cA
    @9
    difss
    cA
    cB
    @14
    cF
    fssres
    mpan2
    @1
    @14
    cB
    @11
    @16
    @1
    @16
    cF
    cA
    cres
    #
    @10
    cres
    #
    @11
    @19
    cF
    cA
    @10
    cin
    #
    cres
    @16
    cF
    cA
    @10
    resres
    @20
    @14
    cF
    cA
    @9
    invdif
    reseq2i
    eqtri
    @1
    @18
    cF
    @10
    @1
    cF
    cA
    wfn
    @18
    cF
    wceq
    cA
    cB
    cF
    ffn
    cA
    cF
    fnresdm
    syl
    reseq1d
    syl5reqr
    feq1d
    mpbird
    adantl
    cA
    cB
    @11
    cX
    cY
    fsnunf2
    syl3an1
    @5
    @0
    @4
    @8
    @13
    wb
    @0
    @1
    @3
    @4
    simp1l
    @2
    @3
    @4
    simp3
    @0
    @4
    wa
    cA
    cB
    @7
    @12
    cX
    cY
    cF
    cV
    cB
    setsval
    feq1d
    syl2anc
    mpbird
end
