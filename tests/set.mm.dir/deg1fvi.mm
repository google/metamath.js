include "cid.mm"
include "cfv.mm"
include "cdg1.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvi.mm"
include "fveq2d.mm"
include "wn.mm"
include "c0.mm"
include "wfn.mm"
include "cxr.mm"
include "wf.mm"
include "cpl1.mm"
include "eqid.mm"
include "00ply1bas.mm"
include "deg1xrf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fn0.mm"
include "mpbi.mm"
include "fvprc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqcomi.mm"

theorem deg1fvi
  let cR: class R


  assert |- ( deg1 ` R ) = ( deg1 ` ( _I ` R ) )

  proof
    cR
    cid
    cfv
    #
    cdg1
    cfv
    #
    cR
    cdg1
    cfv
    #
    cR
    cvv
    wcel
    #
    @1
    @2
    wceq
    @3
    @0
    cR
    cdg1
    cR
    cvv
    fvi
    fveq2d
    @3
    wn
    #
    c0
    cdg1
    cfv
    #
    c0
    @1
    @2
    @5
    c0
    wfn
    #
    @5
    c0
    wceq
    c0
    cxr
    @5
    wf
    @6
    c0
    @5
    c0
    cpl1
    cfv
    #
    c0
    @5
    eqid
    @7
    eqid
    00ply1bas
    deg1xrf
    c0
    cxr
    @5
    ffn
    ax-mp
    @5
    fn0
    mpbi
    @4
    @0
    c0
    cdg1
    cR
    cid
    fvprc
    fveq2d
    cR
    cdg1
    fvprc
    3eqtr4a
    pm2.61i
    eqcomi
end
