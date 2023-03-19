include "cminusg.mm"
include "cfv.mm"
include "cid.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvi.mm"
include "fveq2d.mm"
include "wn.mm"
include "c0.mm"
include "wfn.mm"
include "base0.mm"
include "eqid.mm"
include "grpinvfn.mm"
include "fn0.mm"
include "mpbi.mm"
include "fvprc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtr4i.mm"

theorem grpinvfvi
  let cG: class G
  let cN: class N
  assume grpinvfvi.t: |- N = ( invg ` G )


  assert |- N = ( invg ` ( _I ` G ) )

  proof
    cN
    cG
    cminusg
    cfv
    #
    cG
    cid
    cfv
    #
    cminusg
    cfv
    #
    grpinvfvi.t
    cG
    cvv
    wcel
    #
    @2
    @0
    wceq
    @3
    @1
    cG
    cminusg
    cG
    cvv
    fvi
    fveq2d
    @3
    wn
    #
    c0
    cminusg
    cfv
    #
    c0
    @2
    @0
    @5
    c0
    wfn
    @5
    c0
    wceq
    c0
    c0
    @5
    base0
    @5
    eqid
    grpinvfn
    @5
    fn0
    mpbi
    @4
    @1
    c0
    cminusg
    cG
    cid
    fvprc
    fveq2d
    cG
    cminusg
    fvprc
    3eqtr4a
    pm2.61i
    eqtr4i
end
