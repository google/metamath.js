include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cuhgr.mm"
include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "ccplgr.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wb.mm"
include "simpl.mm"
include "fveq2.mm"
include "adantl.mm"
include "cvv.mm"
include "elex.mm"
include "id.mm"
include "hashprb.mm"
include "biimpi.mm"
include "syl3an.mm"
include "sylan9eqr.mm"
include "cplgr2v.mm"
include "syl2an2.mm"
include "simprr.mm"
include "eleq1d.mm"
include "bitrd.mm"

theorem cplgr2vpr
  let cA: class A
  let cB: class B
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let vv: setvar v
  let vn: setvar n
  assume cplgr0v.v: |- V = ( Vtx ` G )
  assume cplgr2v.e: |- E = ( Edg ` G )


  assert |- ( ( ( A e. X /\ B e. Y /\ A =/= B ) /\ ( G e. UHGraph /\ V = { A , B } ) ) -> ( G e. ComplGraph <-> { A , B } e. E ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cG
    cuhgr
    wcel
    #
    cV
    cA
    cB
    cpr
    #
    wceq
    #
    wa
    #
    wa
    #
    cG
    ccplgr
    wcel
    #
    cV
    cE
    wcel
    #
    @5
    cE
    wcel
    @7
    @4
    @3
    cV
    chash
    cfv
    #
    c2
    wceq
    @9
    @10
    wb
    @4
    @6
    simpl
    @7
    @3
    @11
    @5
    chash
    cfv
    #
    c2
    @6
    @11
    @12
    wceq
    @4
    cV
    @5
    chash
    fveq2
    adantl
    @0
    cA
    cvv
    wcel
    #
    @1
    cB
    cvv
    wcel
    #
    @2
    @2
    @12
    c2
    wceq
    #
    cA
    cX
    elex
    cB
    cY
    elex
    @2
    id
    @13
    @14
    @2
    w3a
    @15
    cA
    cB
    hashprb
    biimpi
    syl3an
    sylan9eqr
    cE
    cG
    cV
    cplgr0v.v
    cplgr2v.e
    cplgr2v
    syl2an2
    @8
    cV
    @5
    cE
    @3
    @4
    @6
    simprr
    eleq1d
    bitrd
end
