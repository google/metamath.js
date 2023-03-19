include "wcel.mm"
include "cvv.mm"
include "cfn.mm"
include "wn.mm"
include "chash.mm"
include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "elex.mm"
include "wa.mm"
include "cdif.mm"
include "eldif.mm"
include "cres.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "com.mm"
include "ccrd.mm"
include "ccom.mm"
include "cun.mm"
include "df-hash.mm"
include "reseq1i.mm"
include "resundir.mm"
include "c0.mm"
include "cin.mm"
include "disjdif.mm"
include "cn0.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "eqid.mm"
include "hashkf.mm"
include "ffn.mm"
include "fnresdisj.mm"
include "mp2b.mm"
include "mpbi.mm"
include "pnfex.mm"
include "fconst.mm"
include "fnresdm.mm"
include "uneq12i.mm"
include "uncom.mm"
include "un0.mm"
include "3eqtri.mm"
include "fveq1i.mm"
include "fvres.mm"
include "fvconst2.mm"
include "3eqtr3a.mm"
include "sylbir.mm"
include "sylan.mm"

theorem hashinf
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. V /\ -. A e. Fin ) -> ( # ` A ) = +oo )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cA
    cfn
    wcel
    wn
    #
    cA
    chash
    cfv
    #
    cpnf
    wceq
    #
    cA
    cV
    elex
    @0
    @1
    wa
    cA
    cvv
    cfn
    cdif
    #
    wcel
    #
    @3
    cA
    cvv
    cfn
    eldif
    @5
    cA
    chash
    @4
    cres
    #
    cfv
    cA
    @4
    cpnf
    csn
    #
    cxp
    #
    cfv
    @2
    cpnf
    cA
    @6
    @8
    @6
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    cc0
    crdg
    com
    cres
    #
    ccrd
    ccom
    #
    @8
    cun
    #
    @4
    cres
    @10
    @4
    cres
    #
    @8
    @4
    cres
    #
    cun
    #
    @8
    chash
    @11
    @4
    vx
    df-hash
    reseq1i
    @10
    @8
    @4
    resundir
    @14
    c0
    @8
    cun
    @8
    c0
    cun
    @8
    @12
    c0
    @13
    @8
    cfn
    @4
    cin
    c0
    wceq
    #
    @12
    c0
    wceq
    #
    cfn
    cvv
    disjdif
    cfn
    cn0
    @10
    wf
    @10
    cfn
    wfn
    @15
    @16
    wb
    vx
    @9
    @10
    @9
    eqid
    @10
    eqid
    hashkf
    cfn
    cn0
    @10
    ffn
    cfn
    @4
    @10
    fnresdisj
    mp2b
    mpbi
    @4
    @7
    @8
    wf
    @8
    @4
    wfn
    @13
    @8
    wceq
    @4
    cpnf
    pnfex
    fconst
    @4
    @7
    @8
    ffn
    @4
    @8
    fnresdm
    mp2b
    uneq12i
    c0
    @8
    uncom
    @8
    un0
    3eqtri
    3eqtri
    fveq1i
    cA
    @4
    chash
    fvres
    @4
    cpnf
    cA
    pnfex
    fvconst2
    3eqtr3a
    sylbir
    sylan
end
