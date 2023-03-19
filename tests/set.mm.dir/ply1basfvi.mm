include "cvv.mm"
include "wcel.mm"
include "cpl1.mm"
include "cfv.mm"
include "cbs.mm"
include "cid.mm"
include "wceq.mm"
include "fvi.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "wn.mm"
include "c0.mm"
include "base0.mm"
include "00ply1bas.mm"
include "eqtr3i.mm"
include "fvprc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem ply1basfvi
  let cR: class R


  assert |- ( Base ` ( Poly1 ` R ) ) = ( Base ` ( Poly1 ` ( _I ` R ) ) )

  proof
    cR
    cvv
    wcel
    #
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    cR
    cid
    cfv
    #
    cpl1
    cfv
    #
    cbs
    cfv
    #
    wceq
    @0
    @1
    @4
    cbs
    @0
    cR
    @3
    cpl1
    @0
    @3
    cR
    cR
    cvv
    fvi
    eqcomd
    fveq2d
    fveq2d
    @0
    wn
    #
    c0
    cbs
    cfv
    #
    c0
    cpl1
    cfv
    #
    cbs
    cfv
    #
    @2
    @5
    c0
    @7
    @9
    base0
    00ply1bas
    eqtr3i
    @6
    @1
    c0
    cbs
    cR
    cpl1
    fvprc
    fveq2d
    @6
    @4
    @8
    cbs
    @6
    @3
    c0
    cpl1
    cR
    cid
    fvprc
    fveq2d
    fveq2d
    3eqtr4a
    pm2.61i
end
