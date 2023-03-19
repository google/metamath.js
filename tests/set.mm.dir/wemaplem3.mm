include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wb.mm"
include "wemaplem1.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cvv.mm"
include "ad2antrr.mm"
include "wor.mm"
include "wpo.mm"
include "simplrl.mm"
include "simp2rl.mm"
include "3expa.mm"
include "simprr.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "wemaplem2.mm"
include "rexlimdvaa.mm"
include "mp2d.mm"

theorem wemaplem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cX: class X
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cU: class U
  let cZ: class Z
  assume wemapso.t: |- T = { <. x , y >. | E. z e. A ( ( x ` z ) S ( y ` z ) /\ A. w e. A ( w R z -> ( x ` w ) = ( y ` w ) ) ) }
  assume wemaplem2.a: |- ( ph -> A e. _V )
  assume wemaplem2.p: |- ( ph -> P e. ( B ^m A ) )
  assume wemaplem2.x: |- ( ph -> X e. ( B ^m A ) )
  assume wemaplem2.q: |- ( ph -> Q e. ( B ^m A ) )
  assume wemaplem2.r: |- ( ph -> R Or A )
  assume wemaplem2.s: |- ( ph -> S Po B )
  assume wemaplem3.px: |- ( ph -> P T X )
  assume wemaplem3.xq: |- ( ph -> X T Q )

  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint X w
  disjoint x y
  disjoint x z
  disjoint X x
  disjoint y z
  disjoint X y
  disjoint X z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint d ph
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint B b
  disjoint c d
  disjoint c x
  disjoint B c
  disjoint d x
  disjoint B d
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint X a
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint X b
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint X c
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q d
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint Z c
  disjoint Z d
  disjoint Z x
  assert |- ( ph -> P T Q )

  proof
    wph
    va
    cv
    #
    cP
    cfv
    @0
    cX
    cfv
    cS
    wbr
    #
    vc
    cv
    #
    @0
    cR
    wbr
    @2
    cP
    cfv
    @2
    cX
    cfv
    #
    wceq
    wi
    vc
    cA
    wral
    #
    wa
    #
    va
    cA
    wrex
    #
    vb
    cv
    #
    cX
    cfv
    @7
    cQ
    cfv
    cS
    wbr
    #
    @2
    @7
    cR
    wbr
    @3
    @2
    cQ
    cfv
    wceq
    wi
    vc
    cA
    wral
    #
    wa
    #
    vb
    cA
    wrex
    #
    cP
    cQ
    cT
    wbr
    #
    wph
    cP
    cX
    cT
    wbr
    #
    @6
    wemaplem3.px
    wph
    cP
    cB
    cA
    cmap
    co
    #
    wcel
    #
    cX
    @14
    wcel
    #
    @13
    @6
    wb
    wemaplem2.p
    wemaplem2.x
    vx
    vy
    vz
    vw
    cA
    cP
    cX
    cR
    cS
    cT
    @14
    @14
    va
    vc
    wemapso.t
    wemaplem1
    syl2anc
    mpbid
    wph
    cX
    cQ
    cT
    wbr
    #
    @11
    wemaplem3.xq
    wph
    @16
    cQ
    @14
    wcel
    #
    @17
    @11
    wb
    wemaplem2.x
    wemaplem2.q
    vx
    vy
    vz
    vw
    cA
    cX
    cQ
    cR
    cS
    cT
    @14
    @14
    vb
    vc
    wemapso.t
    wemaplem1
    syl2anc
    mpbid
    wph
    @5
    @11
    @12
    wi
    va
    cA
    wph
    @0
    cA
    wcel
    #
    @5
    wa
    #
    wa
    #
    @10
    @12
    vb
    cA
    @21
    @7
    cA
    wcel
    #
    @10
    wa
    #
    wa
    vx
    vy
    vz
    vw
    cA
    cB
    cP
    cQ
    cR
    cS
    cT
    cX
    va
    vb
    vc
    wemapso.t
    wph
    cA
    cvv
    wcel
    @20
    @23
    wemaplem2.a
    ad2antrr
    wph
    @15
    @20
    @23
    wemaplem2.p
    ad2antrr
    wph
    @16
    @20
    @23
    wemaplem2.x
    ad2antrr
    wph
    @18
    @20
    @23
    wemaplem2.q
    ad2antrr
    wph
    cA
    cR
    wor
    @20
    @23
    wemaplem2.r
    ad2antrr
    wph
    cB
    cS
    wpo
    @20
    @23
    wemaplem2.s
    ad2antrr
    wph
    @19
    @5
    @23
    simplrl
    wph
    @20
    @23
    @1
    @1
    @4
    @19
    wph
    @23
    simp2rl
    3expa
    @20
    @4
    wph
    @23
    @19
    @1
    @4
    simprr
    ad2antlr
    @21
    @22
    @10
    simprl
    @21
    @22
    @8
    @9
    simprrl
    @21
    @22
    @8
    @9
    simprrr
    wemaplem2
    rexlimdvaa
    rexlimdvaa
    mp2d
end
