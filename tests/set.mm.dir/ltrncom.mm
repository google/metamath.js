include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ccom.mm"
include "wceq.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "eqid.mm"
include "cdlemg47a.mm"
include "syl121anc.mm"
include "wne.mm"
include "ctrl.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpll3.mm"
include "simplr.mm"
include "cdlemg48.mm"
include "syl122anc.mm"
include "cdlemg44.mm"
include "pm2.61dane.mm"

theorem ltrncom
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume ltrncom.h: |- H = ( LHyp ` K )
  assume ltrncom.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) -> ( F o. G ) = ( G o. F ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
    #
    cF
    cG
    ccom
    cG
    cF
    ccom
    wceq
    #
    cF
    cid
    cK
    cbs
    cfv
    #
    cres
    #
    @3
    cF
    @6
    wceq
    #
    wa
    @0
    @1
    @2
    @7
    @4
    @0
    @1
    @2
    @7
    simpl1
    @0
    @1
    @2
    @7
    simpl2
    @0
    @1
    @2
    @7
    simpl3
    @3
    @7
    simpr
    @5
    cT
    cF
    cG
    cH
    cK
    cW
    @5
    eqid
    #
    ltrncom.h
    ltrncom.t
    cdlemg47a
    syl121anc
    @3
    cF
    @6
    wne
    #
    wa
    #
    @4
    cF
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    #
    cG
    @11
    cfv
    #
    @10
    @12
    @13
    wceq
    #
    wa
    @0
    @1
    @2
    @9
    @14
    @4
    @0
    @1
    @2
    @9
    @14
    simpll1
    @0
    @1
    @2
    @9
    @14
    simpll2
    @0
    @1
    @2
    @9
    @14
    simpll3
    @3
    @9
    @14
    simplr
    @10
    @14
    simpr
    @5
    @11
    cT
    cF
    cG
    cH
    cK
    cW
    @8
    ltrncom.h
    ltrncom.t
    @11
    eqid
    #
    cdlemg48
    syl122anc
    @10
    @12
    @13
    wne
    #
    wa
    @0
    @1
    @2
    @16
    @4
    @0
    @1
    @2
    @9
    @16
    simpll1
    @0
    @1
    @2
    @9
    @16
    simpll2
    @0
    @1
    @2
    @9
    @16
    simpll3
    @10
    @16
    simpr
    @11
    cT
    cF
    cG
    cH
    cK
    cW
    ltrncom.h
    ltrncom.t
    @15
    cdlemg44
    syl121anc
    pm2.61dane
    pm2.61dane
end
