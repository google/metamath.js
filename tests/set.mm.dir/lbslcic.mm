include "clmod.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "wf1o.mm"
include "cfrlm.mm"
include "co.mm"
include "clmic.mm"
include "wex.mm"
include "simp3.mm"
include "bren.mm"
include "sylib.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cvsca.mm"
include "cof.mm"
include "cgsu.mm"
include "cmpt.mm"
include "clmim.mm"
include "ccnv.mm"
include "clspn.mm"
include "cvv.mm"
include "eqid.mm"
include "simpl1.mm"
include "relen.mm"
include "brrelexi.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "csca.mm"
include "wceq.mm"
include "a1i.mm"
include "wfo.mm"
include "f1ofo.mm"
include "adantl.mm"
include "clinds.mm"
include "wf1.mm"
include "clindf.mm"
include "lbslinds.mm"
include "sseli.mm"
include "3ad2ant2.mm"
include "f1of1.mm"
include "f1linds.mm"
include "syl3anc.mm"
include "lbssp.mm"
include "indlcim.mm"
include "lmimcnv.mm"
include "brlmici.mm"
include "3syl.mm"
include "exlimddv.mm"

theorem lbslcic
  let cB: class B
  let cF: class F
  let cI: class I
  let cJ: class J
  let cW: class W
  let ve: setvar e
  let vx: setvar x
  assume lbslcic.f: |- F = ( Scalar ` W )
  assume lbslcic.j: |- J = ( LBasis ` W )


  assert |- ( ( W e. LMod /\ B e. J /\ I ~~ B ) -> W ~=m ( F freeLMod I ) )

  proof
    cW
    clmod
    wcel
    #
    cB
    cJ
    wcel
    #
    cI
    cB
    cen
    wbr
    #
    w3a
    #
    cI
    cB
    ve
    cv
    #
    wf1o
    #
    cW
    cF
    cI
    cfrlm
    co
    #
    clmic
    wbr
    #
    ve
    @3
    @2
    @5
    ve
    wex
    @0
    @1
    @2
    simp3
    cI
    cB
    ve
    bren
    sylib
    @3
    @5
    wa
    #
    vx
    @6
    cbs
    cfv
    #
    cW
    vx
    cv
    @4
    cW
    cvsca
    cfv
    #
    cof
    co
    cgsu
    co
    cmpt
    #
    @6
    cW
    clmim
    co
    wcel
    @11
    ccnv
    #
    cW
    @6
    clmim
    co
    wcel
    @7
    @8
    vx
    @4
    @9
    cW
    cbs
    cfv
    #
    cF
    cW
    @10
    @11
    @6
    cI
    cB
    cW
    clspn
    cfv
    #
    cvv
    @6
    eqid
    @9
    eqid
    @13
    eqid
    #
    @10
    eqid
    @14
    eqid
    #
    @11
    eqid
    @0
    @1
    @2
    @5
    simpl1
    #
    @3
    cI
    cvv
    wcel
    #
    @5
    @2
    @0
    @18
    @1
    cI
    cB
    cen
    relen
    brrelexi
    3ad2ant3
    adantr
    cF
    cW
    csca
    cfv
    wceq
    @8
    lbslcic.f
    a1i
    @5
    cI
    cB
    @4
    wfo
    @3
    cI
    cB
    @4
    f1ofo
    adantl
    @8
    @0
    cB
    cW
    clinds
    cfv
    #
    wcel
    #
    cI
    cB
    @4
    wf1
    #
    @4
    cW
    clindf
    wbr
    @17
    @3
    @20
    @5
    @1
    @0
    @20
    @2
    cJ
    @19
    cB
    cJ
    cW
    lbslcic.j
    lbslinds
    sseli
    3ad2ant2
    adantr
    @5
    @21
    @3
    cI
    cB
    @4
    f1of1
    adantl
    cI
    cB
    @4
    cW
    f1linds
    syl3anc
    @3
    cB
    @14
    cfv
    @13
    wceq
    #
    @5
    @1
    @0
    @22
    @2
    cB
    cJ
    @14
    @13
    cW
    @15
    lbslcic.j
    @16
    lbssp
    3ad2ant2
    adantr
    indlcim
    @6
    cW
    @11
    lmimcnv
    cW
    @6
    @12
    brlmici
    3syl
    exlimddv
end
