include "cupgr.mm"
include "wcel.mm"
include "wfn.mm"
include "w3a.mm"
include "cfv.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "ssrab2.mm"
include "wa.mm"
include "upgrfn.mm"
include "ffvelrnda.mm"
include "3impa.mm"
include "sseldi.mm"
include "eldifsni.mm"
include "syl.mm"

theorem upgrn0
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


  assert |- ( ( G e. UPGraph /\ E Fn A /\ F e. A ) -> ( E ` F ) =/= (/) )

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
    #
    cF
    cE
    cfv
    #
    cV
    cpw
    #
    c0
    csn
    cdif
    #
    wcel
    @4
    c0
    wne
    @3
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    #
    vx
    @6
    crab
    #
    @6
    @4
    @7
    vx
    @6
    ssrab2
    @0
    @1
    @2
    @4
    @8
    wcel
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
    sseldi
    @4
    @5
    c0
    eldifsni
    syl
end
