include "cupgr.mm"
include "wcel.mm"
include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cdvds.mm"
include "wn.mm"
include "crab.mm"
include "chash.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "cpr.mm"
include "cif.mm"
include "ciedg.mm"
include "eqid.mm"
include "simpl.mm"
include "wfun.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "uhgrfun.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "eupth2.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "hash0.mm"
include "c0ex.mm"
include "prid1.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wne.mm"
include "neqned.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "hashprg.mm"
include "mp2an.mm"
include "sylib.mm"
include "2ex.mm"
include "prid2.mm"
include "syl6eqel.mm"
include "ifbothda.mm"
include "eqeltrd.mm"

theorem eulerpathpr
  let vx: setvar x
  let cP: class P
  let cF: class F
  let cG: class G
  let cV: class V
  assume eulerpathpr.v: |- V = ( Vtx ` G )

  disjoint F x
  disjoint G x
  disjoint P x
  disjoint V x
  assert |- ( ( G e. UPGraph /\ F ( EulerPaths ` G ) P ) -> ( # ` { x e. V | -. 2 || ( ( VtxDeg ` G ) ` x ) } ) e. { 0 , 2 } )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    #
    wa
    #
    c2
    vx
    cv
    cG
    cvtxdg
    cfv
    cfv
    cdvds
    wbr
    wn
    vx
    cV
    crab
    #
    chash
    cfv
    cc0
    cP
    cfv
    #
    cF
    chash
    cfv
    #
    cP
    cfv
    #
    wceq
    #
    c0
    @4
    @6
    cpr
    #
    cif
    #
    chash
    cfv
    #
    cc0
    c2
    cpr
    #
    @2
    @3
    @9
    chash
    @2
    vx
    cP
    cF
    cG
    cG
    ciedg
    cfv
    #
    cV
    eulerpathpr.v
    @12
    eqid
    #
    @0
    @1
    simpl
    @0
    @12
    wfun
    #
    @1
    @0
    cG
    cuhgr
    wcel
    @14
    cG
    upgruhgr
    @12
    cG
    @13
    uhgrfun
    syl
    adantr
    @0
    @1
    simpr
    eupth2
    fveq2d
    @7
    c0
    chash
    cfv
    #
    @11
    wcel
    #
    @8
    chash
    cfv
    #
    @11
    wcel
    @10
    @11
    wcel
    @2
    c0
    @8
    c0
    @9
    wceq
    @15
    @10
    @11
    c0
    @9
    chash
    fveq2
    eleq1d
    @8
    @9
    wceq
    @17
    @10
    @11
    @8
    @9
    chash
    fveq2
    eleq1d
    @16
    @2
    @7
    wa
    @15
    cc0
    @11
    hash0
    cc0
    c2
    c0ex
    prid1
    eqeltri
    a1i
    @2
    @7
    wn
    #
    wa
    #
    @17
    c2
    @11
    @19
    @4
    @6
    wne
    #
    @17
    c2
    wceq
    #
    @19
    @4
    @6
    @2
    @18
    simpr
    neqned
    @4
    cvv
    wcel
    @6
    cvv
    wcel
    @20
    @21
    wb
    cc0
    cP
    fvex
    @5
    cP
    fvex
    @4
    @6
    cvv
    cvv
    hashprg
    mp2an
    sylib
    cc0
    c2
    2ex
    prid2
    syl6eqel
    ifbothda
    eqeltrd
end
