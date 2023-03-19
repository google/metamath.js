include "cstr.mm"
include "wbr.mm"
include "ccnv.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "wcel.mm"
include "wn.mm"
include "cvv.mm"
include "cxp.mm"
include "0nelxp.mm"
include "cnvcnv.mm"
include "inss2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "mto.mm"
include "disjsn.mm"
include "mpbir.mm"
include "wb.mm"
include "cnvcnvss.mm"
include "reldisj.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "a1i.mm"
include "wrel.mm"
include "wfun.mm"
include "structn0fun.mm"
include "funrel.mm"
include "syl.mm"
include "dfrel2.mm"
include "sylib.mm"
include "difss.mm"
include "cnvss.mm"
include "mp2b.mm"
include "syl6eqssr.mm"
include "eqssd.mm"

theorem structcnvcnv
  let cF: class F
  let cX: class X


  assert |- ( F Struct X -> `' `' F = ( F \ { (/) } ) )

  proof
    cF
    cX
    cstr
    wbr
    #
    cF
    ccnv
    #
    ccnv
    #
    cF
    c0
    csn
    #
    cdif
    #
    @2
    @4
    wss
    #
    @0
    @2
    @3
    cin
    c0
    wceq
    #
    @5
    @6
    c0
    @2
    wcel
    #
    wn
    @7
    c0
    cvv
    cvv
    cxp
    #
    wcel
    cvv
    cvv
    0nelxp
    @2
    @8
    c0
    @2
    cF
    @8
    cin
    @8
    cF
    cnvcnv
    cF
    @8
    inss2
    eqsstri
    sseli
    mto
    @2
    c0
    disjsn
    mpbir
    @2
    cF
    wss
    @6
    @5
    wb
    cF
    cnvcnvss
    @2
    @3
    cF
    reldisj
    ax-mp
    mpbi
    a1i
    @0
    @4
    @4
    ccnv
    #
    ccnv
    #
    @2
    @0
    @4
    wrel
    #
    @10
    @4
    wceq
    @0
    @4
    wfun
    @11
    cF
    cX
    structn0fun
    @4
    funrel
    syl
    @4
    dfrel2
    sylib
    @4
    cF
    wss
    @9
    @1
    wss
    @10
    @2
    wss
    cF
    @3
    difss
    @4
    cF
    cnvss
    @9
    @1
    cnvss
    mp2b
    syl6eqssr
    eqssd
end
