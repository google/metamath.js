include "crg.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cres.mm"
include "cfrlm.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "csn.mm"
include "cxp.mm"
include "cvv.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "ssexd.mm"
include "eqid.mm"
include "frlm0.mm"
include "syl2anc.mm"
include "eqeq2d.mm"
include "rabbidv.mm"
include "syl5eq.mm"
include "cmpt.mm"
include "clmhm.mm"
include "cbs.mm"
include "frlmsplit2.mm"
include "ccnv.mm"
include "cima.mm"
include "fvex.mm"
include "mptiniseg.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "lmhmkerlss.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem frlmsslss
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cR: class R
  let cU: class U
  let cI: class I
  let cJ: class J
  let cV: class V
  let cY: class Y
  let c.0: class .0.
  assume frlmsslss.y: |- Y = ( R freeLMod I )
  assume frlmsslss.u: |- U = ( LSubSp ` Y )
  assume frlmsslss.b: |- B = ( Base ` Y )
  assume frlmsslss.z: |- .0. = ( 0g ` R )
  assume frlmsslss.c: |- C = { x e. B | ( x |` J ) = ( J X. { .0. } ) }

  disjoint B x
  disjoint I x
  disjoint J x
  disjoint R x
  disjoint U x
  disjoint .0. x
  disjoint V x
  disjoint Y x
  assert |- ( ( R e. Ring /\ I e. V /\ J C_ I ) -> C e. U )

  proof
    cR
    crg
    wcel
    #
    cI
    cV
    wcel
    #
    cJ
    cI
    wss
    #
    w3a
    #
    cC
    vx
    cv
    cJ
    cres
    #
    cR
    cJ
    cfrlm
    co
    #
    c0g
    cfv
    #
    wceq
    #
    vx
    cB
    crab
    #
    cU
    @3
    cC
    @4
    cJ
    c.0
    csn
    cxp
    #
    wceq
    #
    vx
    cB
    crab
    @8
    frlmsslss.c
    @3
    @10
    @7
    vx
    cB
    @3
    @9
    @6
    @4
    @3
    @0
    cJ
    cvv
    wcel
    @9
    @6
    wceq
    @0
    @1
    @2
    simp1
    @3
    cJ
    cI
    cV
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    ssexd
    cR
    @5
    cJ
    cvv
    c.0
    @5
    eqid
    #
    frlmsslss.z
    frlm0
    syl2anc
    eqeq2d
    rabbidv
    syl5eq
    @3
    vx
    cB
    @4
    cmpt
    #
    cY
    @5
    clmhm
    co
    wcel
    @8
    cU
    wcel
    vx
    cB
    @5
    cbs
    cfv
    #
    cR
    cI
    @12
    cJ
    cV
    cY
    @5
    frlmsslss.y
    @11
    frlmsslss.b
    @13
    eqid
    @12
    eqid
    #
    frlmsplit2
    cY
    @5
    cU
    @12
    @8
    @6
    @12
    ccnv
    @6
    csn
    cima
    #
    @8
    @6
    cvv
    wcel
    @15
    @8
    wceq
    @5
    c0g
    fvex
    vx
    cB
    @4
    @6
    @12
    cvv
    @14
    mptiniseg
    ax-mp
    eqcomi
    @6
    eqid
    frlmsslss.u
    lmhmkerlss
    syl
    eqeltrd
end
