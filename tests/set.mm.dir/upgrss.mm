include "cupgr.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
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
include "ssrab2.mm"
include "difss.mm"
include "sstri.mm"
include "upgrf.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "elpwid.mm"

theorem upgrss
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


  assert |- ( ( G e. UPGraph /\ F e. dom E ) -> ( E ` F ) C_ V )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cE
    cdm
    #
    wcel
    wa
    #
    cF
    cE
    cfv
    #
    cV
    @2
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    #
    vx
    cV
    cpw
    #
    c0
    csn
    #
    cdif
    #
    crab
    #
    @5
    @3
    @8
    @7
    @5
    @4
    vx
    @7
    ssrab2
    @5
    @6
    difss
    sstri
    @0
    @1
    @8
    cF
    cE
    vx
    cE
    cG
    cV
    isupgr.v
    isupgr.e
    upgrf
    ffvelrnda
    sseldi
    elpwid
end
