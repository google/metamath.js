include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cres.mm"
include "cfv.mm"
include "ccrd.mm"
include "ccom.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crdg.mm"
include "com.mm"
include "cdif.mm"
include "cpnf.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "resundir.mm"
include "c0.mm"
include "cn0.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "eqid.mm"
include "hashkf.mm"
include "ffn.mm"
include "fnresdm.mm"
include "mp2b.mm"
include "cin.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "wb.mm"
include "pnfex.mm"
include "fconst.mm"
include "fnresdisj.mm"
include "mpbi.mm"
include "uneq12i.mm"
include "un0.mm"
include "df-hash.mm"
include "reseq1i.mm"
include "coeq1i.mm"
include "3eqtr4i.mm"
include "fveq1i.mm"
include "wfun.mm"
include "cdm.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "cardf2.mm"
include "ffun.mm"
include "ax-mp.mm"
include "finnum.mm"
include "fvco.mm"
include "sylancr.mm"
include "syl5eq.mm"
include "fvres.mm"
include "eqtr3d.mm"

theorem hashgval
  let vx: setvar x
  let cA: class A
  let cG: class G
  let vy: setvar y
  let cK: class K
  assume hashgval.1: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , 0 ) |` _om )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint K y
  assert |- ( A e. Fin -> ( G ` ( card ` A ) ) = ( # ` A ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    chash
    cfn
    cres
    #
    cfv
    #
    cA
    ccrd
    cfv
    cG
    cfv
    #
    cA
    chash
    cfv
    @0
    @2
    cA
    cG
    ccrd
    ccom
    #
    cfv
    #
    @3
    cA
    @1
    @4
    vx
    cvv
    vx
    cv
    #
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
    cvv
    cfn
    cdif
    #
    cpnf
    csn
    #
    cxp
    #
    cun
    #
    cfn
    cres
    #
    @8
    @1
    @4
    @13
    @8
    cfn
    cres
    #
    @11
    cfn
    cres
    #
    cun
    #
    @8
    @8
    @11
    cfn
    resundir
    @16
    @8
    c0
    cun
    @8
    @14
    @8
    @15
    c0
    cfn
    cn0
    @8
    wf
    @8
    cfn
    wfn
    @14
    @8
    wceq
    vx
    @7
    @8
    @7
    eqid
    @8
    eqid
    hashkf
    cfn
    cn0
    @8
    ffn
    cfn
    @8
    fnresdm
    mp2b
    @9
    cfn
    cin
    #
    c0
    wceq
    #
    @15
    c0
    wceq
    #
    @17
    cfn
    @9
    cin
    c0
    @9
    cfn
    incom
    cfn
    cvv
    disjdif
    eqtri
    @9
    @10
    @11
    wf
    @11
    @9
    wfn
    @18
    @19
    wb
    @9
    cpnf
    pnfex
    fconst
    @9
    @10
    @11
    ffn
    @9
    cfn
    @11
    fnresdisj
    mp2b
    mpbi
    uneq12i
    @8
    un0
    eqtri
    eqtri
    chash
    @12
    cfn
    vx
    df-hash
    reseq1i
    cG
    @7
    ccrd
    hashgval.1
    coeq1i
    3eqtr4i
    fveq1i
    @0
    ccrd
    wfun
    #
    cA
    ccrd
    cdm
    wcel
    @5
    @3
    wceq
    vy
    cv
    @6
    cen
    wbr
    vy
    con0
    wrex
    vx
    cab
    #
    con0
    ccrd
    wf
    @20
    vx
    vy
    cardf2
    @21
    con0
    ccrd
    ffun
    ax-mp
    cA
    finnum
    cA
    cG
    ccrd
    fvco
    sylancr
    syl5eq
    cA
    cfn
    chash
    fvres
    eqtr3d
end
