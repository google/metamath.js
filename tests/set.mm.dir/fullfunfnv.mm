include "cfullfn.mm"
include "cvv.mm"
include "wfn.mm"
include "cfunpart.mm"
include "cdm.mm"
include "cdif.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "wfun.mm"
include "funpartfun.mm"
include "funfn.mm"
include "mpbi.mm"
include "wf.mm"
include "0ex.mm"
include "fconst.mm"
include "ffn.mm"
include "ax-mp.mm"
include "pm3.2i.mm"
include "disjdif.mm"
include "fnun.mm"
include "mp2an.mm"
include "df-fullfun.mm"
include "fneq1i.mm"
include "unvdif.mm"
include "eqcomi.mm"
include "fneq2i.mm"
include "bitri.mm"
include "mpbir.mm"

theorem fullfunfnv
  let cF: class F


  assert |- FullFun F Fn _V

  proof
    cF
    cfullfn
    #
    cvv
    wfn
    #
    cF
    cfunpart
    #
    cvv
    @2
    cdm
    #
    cdif
    #
    c0
    csn
    #
    cxp
    #
    cun
    #
    @3
    @4
    cun
    #
    wfn
    #
    @2
    @3
    wfn
    #
    @6
    @4
    wfn
    #
    wa
    @3
    @4
    cin
    c0
    wceq
    @9
    @10
    @11
    @2
    wfun
    @10
    cF
    funpartfun
    @2
    funfn
    mpbi
    @4
    @5
    @6
    wf
    @11
    @4
    c0
    0ex
    fconst
    @4
    @5
    @6
    ffn
    ax-mp
    pm3.2i
    @3
    cvv
    disjdif
    @3
    @4
    @2
    @6
    fnun
    mp2an
    @1
    @7
    cvv
    wfn
    @9
    cvv
    @0
    @7
    cF
    df-fullfun
    fneq1i
    cvv
    @8
    @7
    @8
    cvv
    @3
    unvdif
    eqcomi
    fneq2i
    bitri
    mpbir
end
