include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "cusgr.mm"
include "ciedg.mm"
include "c0.mm"
include "wb.mm"
include "wi.mm"
include "usgr1vr.mm"
include "adantrl.mm"
include "simplrl.mm"
include "simpr.mm"
include "usgr0e.mm"
include "ex.mm"
include "impbid.mm"
include "wn.mm"
include "snprc.mm"
include "simpl.mm"
include "simprr.mm"
include "eqtrd.mm"
include "usgr0vb.mm"
include "syl2an2.mm"
include "sylbi.mm"
include "pm2.61i.mm"

theorem usgr1v
  let cA: class A
  let cG: class G
  let cW: class W
  let vx: setvar x
  let cX: class X


  assert |- ( ( G e. W /\ ( Vtx ` G ) = { A } ) -> ( G e. USGraph <-> ( iEdg ` G ) = (/) ) )

  proof
    cA
    cvv
    wcel
    #
    cG
    cW
    wcel
    #
    cG
    cvtx
    cfv
    #
    cA
    csn
    #
    wceq
    #
    wa
    #
    cG
    cusgr
    wcel
    #
    cG
    ciedg
    cfv
    c0
    wceq
    #
    wb
    #
    wi
    #
    @0
    @5
    @8
    @0
    @5
    wa
    #
    @6
    @7
    @0
    @4
    @6
    @7
    wi
    @1
    cA
    cG
    cvv
    usgr1vr
    adantrl
    @10
    @7
    @6
    @10
    @7
    wa
    cG
    cW
    @0
    @1
    @4
    @7
    simplrl
    @10
    @7
    simpr
    usgr0e
    ex
    impbid
    ex
    @0
    wn
    @3
    c0
    wceq
    #
    @9
    cA
    snprc
    @11
    @5
    @8
    @5
    @1
    @11
    @2
    c0
    wceq
    @8
    @1
    @4
    simpl
    @11
    @5
    wa
    @2
    @3
    c0
    @11
    @1
    @4
    simprr
    @11
    @5
    simpl
    eqtrd
    cG
    cW
    usgr0vb
    syl2an2
    ex
    sylbi
    pm2.61i
end
