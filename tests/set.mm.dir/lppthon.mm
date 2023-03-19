include "cuhgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "w3a.mm"
include "cs2.mm"
include "cs1.mm"
include "cvtx.mm"
include "eqid.mm"
include "lpvtx.mm"
include "simpl3.mm"
include "wne.mm"
include "cpr.mm"
include "wss.mm"
include "wi.mm"
include "eqneqall.mm"
include "ax-mp.mm"
include "adantl.mm"
include "1pthond.mm"

theorem lppthon
  let cA: class A
  let cG: class G
  let cI: class I
  let cJ: class J
  assume lppthon.i: |- I = ( iEdg ` G )


  assert |- ( ( G e. UHGraph /\ J e. dom I /\ ( I ` J ) = { A } ) -> <" J "> ( A ( PathsOn ` G ) A ) <" A A "> )

  proof
    cG
    cuhgr
    wcel
    #
    cJ
    cI
    cdm
    wcel
    #
    cJ
    cI
    cfv
    #
    cA
    csn
    wceq
    #
    w3a
    #
    cA
    cA
    cs2
    #
    cJ
    cs1
    #
    cG
    cI
    cJ
    cG
    cvtx
    cfv
    #
    cA
    cA
    @5
    eqid
    @6
    eqid
    cA
    cG
    cI
    cJ
    lppthon.i
    lpvtx
    #
    @8
    @0
    @1
    @3
    cA
    cA
    wceq
    #
    simpl3
    cA
    cA
    wne
    #
    cA
    cA
    cpr
    @2
    wss
    #
    @4
    @9
    @10
    @11
    wi
    cA
    eqid
    @11
    cA
    cA
    eqneqall
    ax-mp
    adantl
    @7
    eqid
    lppthon.i
    1pthond
end
