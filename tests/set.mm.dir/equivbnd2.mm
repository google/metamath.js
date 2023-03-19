include "ctotbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cbnd.mm"
include "totbndbnd.mm"
include "wa.mm"
include "simpr.mm"
include "cxp.mm"
include "cres.mm"
include "cme.mm"
include "wss.mm"
include "adantr.mm"
include "bnd2lem.mm"
include "sylan.mm"
include "metres2.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "crp.mm"
include "cv.mm"
include "co.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "sselda.mm"
include "anim12dan.mm"
include "adantlr.mm"
include "syldan.mm"
include "wceq.mm"
include "oveqi.mm"
include "ovres.mm"
include "syl5eq.mm"
include "adantl.mm"
include "oveq2d.mm"
include "3brtr4d.mm"
include "equivbnd.mm"
include "biimpar.mm"
include "bndmet.mm"
include "equivtotbnd.mm"
include "ex.mm"
include "impbid2.mm"

theorem equivbnd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume equivbnd2.1: |- ( ph -> M e. ( Met ` X ) )
  assume equivbnd2.2: |- ( ph -> N e. ( Met ` X ) )
  assume equivbnd2.3: |- ( ph -> R e. RR+ )
  assume equivbnd2.4: |- ( ph -> S e. RR+ )
  assume equivbnd2.5: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( x N y ) <_ ( R x. ( x M y ) ) )
  assume equivbnd2.6: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( x M y ) <_ ( S x. ( x N y ) ) )
  assume equivbnd2.7: |- C = ( M |` ( Y X. Y ) )
  assume equivbnd2.8: |- D = ( N |` ( Y X. Y ) )
  assume equivbnd2.9: |- ( ph -> ( C e. ( TotBnd ` Y ) <-> C e. ( Bnd ` Y ) ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( D e. ( TotBnd ` Y ) <-> D e. ( Bnd ` Y ) ) )

  proof
    wph
    cD
    cY
    ctotbnd
    cfv
    #
    wcel
    #
    cD
    cY
    cbnd
    cfv
    #
    wcel
    #
    cD
    cY
    totbndbnd
    wph
    @3
    @1
    wph
    @3
    wa
    #
    vx
    vy
    cR
    cC
    cD
    cY
    wph
    @3
    cC
    @2
    wcel
    #
    cC
    @0
    wcel
    #
    @4
    vx
    vy
    cS
    cD
    cC
    cY
    wph
    @3
    simpr
    @4
    cC
    cM
    cY
    cY
    cxp
    #
    cres
    #
    cY
    cme
    cfv
    #
    equivbnd2.7
    @4
    cM
    cX
    cme
    cfv
    #
    wcel
    #
    cY
    cX
    wss
    #
    @8
    @9
    wcel
    wph
    @11
    @3
    equivbnd2.1
    adantr
    wph
    cN
    @10
    wcel
    @3
    @12
    equivbnd2.2
    cD
    cN
    cX
    cY
    equivbnd2.8
    bnd2lem
    sylan
    #
    cM
    cY
    cX
    metres2
    syl2anc
    syl5eqel
    wph
    cS
    crp
    wcel
    @3
    equivbnd2.4
    adantr
    @4
    vx
    cv
    #
    cY
    wcel
    #
    vy
    cv
    #
    cY
    wcel
    #
    wa
    #
    wa
    #
    @14
    @16
    cM
    co
    #
    cS
    @14
    @16
    cN
    co
    #
    cmul
    co
    #
    @14
    @16
    cC
    co
    #
    cS
    @14
    @16
    cD
    co
    #
    cmul
    co
    cle
    @4
    @18
    @14
    cX
    wcel
    #
    @16
    cX
    wcel
    #
    wa
    #
    @20
    @22
    cle
    wbr
    #
    @4
    @15
    @25
    @17
    @26
    @4
    cY
    cX
    @14
    @13
    sselda
    @4
    cY
    cX
    @16
    @13
    sselda
    anim12dan
    #
    wph
    @27
    @28
    @3
    equivbnd2.6
    adantlr
    syldan
    @18
    @23
    @20
    wceq
    @4
    @18
    @23
    @14
    @16
    @8
    co
    @20
    cC
    @8
    @14
    @16
    equivbnd2.7
    oveqi
    @14
    @16
    cY
    cY
    cM
    ovres
    syl5eq
    adantl
    #
    @19
    @24
    @21
    cS
    cmul
    @18
    @24
    @21
    wceq
    @4
    @18
    @24
    @14
    @16
    cN
    @7
    cres
    #
    co
    @21
    cD
    @31
    @14
    @16
    equivbnd2.8
    oveqi
    @14
    @16
    cY
    cY
    cN
    ovres
    syl5eq
    adantl
    #
    oveq2d
    3brtr4d
    equivbnd
    wph
    @6
    @5
    equivbnd2.9
    biimpar
    syldan
    @3
    cD
    @9
    wcel
    wph
    cD
    cY
    bndmet
    adantl
    wph
    cR
    crp
    wcel
    @3
    equivbnd2.3
    adantr
    @19
    @21
    cR
    @20
    cmul
    co
    #
    @24
    cR
    @23
    cmul
    co
    cle
    @4
    @18
    @27
    @21
    @33
    cle
    wbr
    #
    @29
    wph
    @27
    @34
    @3
    equivbnd2.5
    adantlr
    syldan
    @32
    @19
    @23
    @20
    cR
    cmul
    @30
    oveq2d
    3brtr4d
    equivtotbnd
    ex
    impbid2
end
