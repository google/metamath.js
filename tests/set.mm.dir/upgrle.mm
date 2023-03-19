include "cupgr.mm"
include "wcel.mm"
include "wfn.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wa.mm"
include "upgrfn.mm"
include "ffvelrnda.mm"
include "3impa.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "syl.mm"

theorem upgrle
  let cA: class A
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let ve: setvar e
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let vx: setvar x
  assume isupgr.v: |- V = ( Vtx ` G )
  assume isupgr.e: |- E = ( iEdg ` G )


  assert |- ( ( G e. UPGraph /\ E Fn A /\ F e. A ) -> ( # ` ( E ` F ) ) <_ 2 )

  proof
    cG
    cupgr
    wcel
    #
    cE
    cA
    wfn
    #
    cF
    cA
    wcel
    #
    w3a
    cF
    cE
    cfv
    #
    vx
    cv
    #
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    vx
    cV
    cpw
    c0
    csn
    cdif
    #
    crab
    #
    wcel
    #
    @3
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    @0
    @1
    @2
    @9
    @0
    @1
    wa
    cA
    @8
    cF
    cE
    vx
    cA
    cE
    cG
    cV
    isupgr.v
    isupgr.e
    upgrfn
    ffvelrnda
    3impa
    @9
    @3
    @7
    wcel
    @11
    @6
    @11
    vx
    @3
    @7
    @4
    @3
    wceq
    @5
    @10
    c2
    cle
    @4
    @3
    chash
    fveq2
    breq1d
    elrab
    simprbi
    syl
end
