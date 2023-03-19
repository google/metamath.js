include "cupgr.mm"
include "wcel.mm"
include "wfn.mm"
include "w3a.mm"
include "cfv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cfn.mm"
include "upgrle.mm"
include "wn.mm"
include "cpnf.mm"
include "clt.mm"
include "cr.mm"
include "2re.mm"
include "ltpnf.mm"
include "ax-mp.mm"
include "cxr.mm"
include "wb.mm"
include "rexri.mm"
include "pnfxr.mm"
include "xrltnle.mm"
include "mp2an.mm"
include "mpbi.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "hashinf.mm"
include "mpan.mm"
include "breq1d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "syl.mm"

theorem upgrfi
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


  assert |- ( ( G e. UPGraph /\ E Fn A /\ F e. A ) -> ( E ` F ) e. Fin )

  proof
    cG
    cupgr
    wcel
    cE
    cA
    wfn
    cF
    cA
    wcel
    w3a
    cF
    cE
    cfv
    #
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    @0
    cfn
    wcel
    #
    cA
    cE
    cF
    cG
    cV
    isupgr.v
    isupgr.e
    upgrle
    @3
    @2
    @3
    wn
    #
    @2
    cpnf
    c2
    cle
    wbr
    #
    c2
    cpnf
    clt
    wbr
    #
    @5
    wn
    #
    c2
    cr
    wcel
    @6
    2re
    c2
    ltpnf
    ax-mp
    c2
    cxr
    wcel
    cpnf
    cxr
    wcel
    @6
    @7
    wb
    c2
    2re
    rexri
    pnfxr
    c2
    cpnf
    xrltnle
    mp2an
    mpbi
    @4
    @1
    cpnf
    c2
    cle
    @0
    cvv
    wcel
    @4
    @1
    cpnf
    wceq
    cF
    cE
    fvex
    @0
    cvv
    hashinf
    mpan
    breq1d
    mtbiri
    con4i
    syl
end
