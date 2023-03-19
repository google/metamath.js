include "cupgr.mm"
include "wcel.mm"
include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "ccrcts.mm"
include "w3a.mm"
include "c2.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cdvds.mm"
include "wn.mm"
include "crab.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "c0.mm"
include "cpr.mm"
include "cif.mm"
include "wral.mm"
include "wa.mm"
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
include "3adant3.mm"
include "ctrls.mm"
include "crctprop.mm"
include "simprd.mm"
include "3ad2ant3.mm"
include "iftrued.mm"
include "eqeq2d.mm"
include "rabeq0.mm"
include "notnotr.mm"
include "ralimi.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "mpd.mm"

theorem eulercrct
  let vx: setvar x
  let cP: class P
  let cF: class F
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vp: setvar p
  assume eulerpathpr.v: |- V = ( Vtx ` G )

  disjoint F x
  disjoint G x
  disjoint P x
  disjoint V x
  disjoint G f
  disjoint G p
  disjoint f p
  disjoint V f
  disjoint V p
  disjoint f x
  disjoint p x
  assert |- ( ( G e. UPGraph /\ F ( EulerPaths ` G ) P /\ F ( Circuits ` G ) P ) -> A. x e. V 2 || ( ( VtxDeg ` G ) ` x ) )

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
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    #
    w3a
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
    #
    wn
    #
    vx
    cV
    crab
    #
    cc0
    cP
    cfv
    #
    cF
    chash
    cfv
    cP
    cfv
    #
    wceq
    #
    c0
    @7
    @8
    cpr
    #
    cif
    #
    wceq
    #
    @4
    vx
    cV
    wral
    #
    @0
    @1
    @12
    @2
    @0
    @1
    wa
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
    @14
    eqid
    #
    @0
    @1
    simpl
    @0
    @14
    wfun
    #
    @1
    @0
    cG
    cuhgr
    wcel
    @16
    cG
    upgruhgr
    @14
    cG
    @15
    uhgrfun
    syl
    adantr
    @0
    @1
    simpr
    eupth2
    3adant3
    @3
    @12
    @6
    c0
    wceq
    #
    @13
    @3
    @11
    c0
    @6
    @3
    @9
    c0
    @10
    @2
    @0
    @9
    @1
    @2
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    @9
    cP
    cF
    cG
    crctprop
    simprd
    3ad2ant3
    iftrued
    eqeq2d
    @17
    @5
    wn
    #
    vx
    cV
    wral
    @13
    @5
    vx
    cV
    rabeq0
    @18
    @4
    vx
    cV
    @4
    notnotr
    ralimi
    sylbi
    syl6bi
    mpd
end
