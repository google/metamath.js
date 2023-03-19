include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cfv.mm"
include "ciin.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cint.mm"
include "fvex.mm"
include "dfiin2.mm"
include "clmod.mm"
include "simpl.mm"
include "dvhlmod.mm"
include "wral.mm"
include "simpll.mm"
include "simplrl.mm"
include "simpr.mm"
include "sseldd.mm"
include "dihlss.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "wb.mm"
include "uniiunlem.mm"
include "syl.mm"
include "mpbid.mm"
include "wex.mm"
include "simprr.mm"
include "n0.mm"
include "sylib.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfcv.mm"
include "nfne.mm"
include "elabrex.mm"
include "ne0i.mm"
include "exlimi.mm"
include "lssintcl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"

theorem dihglblem5
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vy: setvar y
  assume dihglblem5.b: |- B = ( Base ` K )
  assume dihglblem5.g: |- G = ( glb ` K )
  assume dihglblem5.h: |- H = ( LHyp ` K )
  assume dihglblem5.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihglblem5.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihglblem5.s: |- S = ( LSubSp ` U )

  disjoint B x
  disjoint H x
  disjoint K x
  disjoint S x
  disjoint T x
  disjoint W x
  disjoint I y
  disjoint x y
  disjoint T y
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( T C_ B /\ T =/= (/) ) ) -> |^|_ x e. T ( I ` x ) e. S )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cT
    cB
    wss
    #
    cT
    c0
    wne
    #
    wa
    #
    wa
    #
    vx
    cT
    vx
    cv
    #
    cI
    cfv
    #
    ciin
    vy
    cv
    @6
    wceq
    #
    vx
    cT
    wrex
    #
    vy
    cab
    #
    cint
    #
    cS
    vx
    vy
    cT
    @6
    @5
    cI
    fvex
    #
    dfiin2
    @4
    cU
    clmod
    wcel
    @9
    cS
    wss
    #
    @9
    c0
    wne
    #
    @10
    cS
    wcel
    @4
    cU
    cH
    cK
    cW
    dihglblem5.h
    dihglblem5.u
    @0
    @3
    simpl
    dvhlmod
    @4
    @6
    cS
    wcel
    #
    vx
    cT
    wral
    #
    @12
    @4
    @14
    vx
    cT
    @4
    @5
    cT
    wcel
    #
    wa
    #
    @0
    @5
    cB
    wcel
    @14
    @0
    @3
    @16
    simpll
    @17
    cT
    cB
    @5
    @0
    @1
    @2
    @16
    simplrl
    @4
    @16
    simpr
    sseldd
    cB
    cS
    cU
    cH
    cI
    cK
    cW
    @5
    dihglblem5.b
    dihglblem5.h
    dihglblem5.i
    dihglblem5.u
    dihglblem5.s
    dihlss
    syl2anc
    ralrimiva
    #
    @4
    @15
    @15
    @12
    wb
    @18
    vx
    vy
    cT
    @6
    cS
    cS
    uniiunlem
    syl
    mpbid
    @4
    @16
    vx
    wex
    #
    @13
    @4
    @2
    @19
    @0
    @1
    @2
    simprr
    vx
    cT
    n0
    sylib
    @16
    @13
    vx
    vx
    @9
    c0
    @8
    vx
    vy
    @7
    vx
    cT
    nfre1
    nfab
    vx
    c0
    nfcv
    nfne
    @16
    @6
    @9
    wcel
    @13
    vx
    vy
    cT
    @6
    @11
    elabrex
    @9
    @6
    ne0i
    syl
    exlimi
    syl
    @9
    cS
    cU
    dihglblem5.s
    lssintcl
    syl3anc
    syl5eqel
end
