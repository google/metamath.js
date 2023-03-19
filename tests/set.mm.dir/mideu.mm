include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "midex.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprl.mm"
include "eqcomd.mm"
include "simprr.mm"
include "miduniq.mm"
include "ex.mm"
include "ralrimivva.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "rmo4.mm"
include "sylibr.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem mideu
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  assume colperpex.p: |- P = ( Base ` G )
  assume colperpex.d: |- .- = ( dist ` G )
  assume colperpex.i: |- I = ( Itv ` G )
  assume colperpex.l: |- L = ( LineG ` G )
  assume colperpex.g: |- ( ph -> G e. TarskiG )
  assume mideu.s: |- S = ( pInvG ` G )
  assume mideu.1: |- ( ph -> A e. P )
  assume mideu.2: |- ( ph -> B e. P )
  assume mideu.3: |- ( ph -> G TarskiGDim>= 2 )

  disjoint .- x
  disjoint A x
  disjoint B x
  disjoint G x
  disjoint I x
  disjoint L x
  disjoint P x
  disjoint S x
  disjoint ph x
  disjoint .- p
  disjoint .- q
  disjoint .- s
  disjoint .- t
  disjoint p q
  disjoint p s
  disjoint p t
  disjoint p x
  disjoint q s
  disjoint q t
  disjoint q x
  disjoint s t
  disjoint s x
  disjoint t x
  disjoint A p
  disjoint A q
  disjoint A s
  disjoint A t
  disjoint A y
  disjoint p y
  disjoint q y
  disjoint s y
  disjoint t y
  disjoint x y
  disjoint B p
  disjoint B q
  disjoint B s
  disjoint B t
  disjoint B y
  disjoint G p
  disjoint G q
  disjoint G s
  disjoint G t
  disjoint I p
  disjoint I q
  disjoint I s
  disjoint I t
  disjoint L p
  disjoint L q
  disjoint L s
  disjoint L t
  disjoint P p
  disjoint P q
  disjoint P s
  disjoint P t
  disjoint P y
  disjoint S p
  disjoint S q
  disjoint S t
  disjoint S y
  disjoint p ph
  disjoint ph q
  disjoint ph s
  disjoint ph t
  disjoint ph y
  assert |- ( ph -> E! x e. P B = ( ( S ` x ) ` A ) )

  proof
    wph
    cB
    cA
    vx
    cv
    #
    cS
    cfv
    #
    cfv
    #
    wceq
    #
    vx
    cP
    wrex
    @3
    vx
    cP
    wrmo
    #
    @3
    vx
    cP
    wreu
    wph
    vx
    cA
    cB
    cP
    cS
    cG
    cI
    cL
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    colperpex.g
    mideu.s
    mideu.1
    mideu.2
    mideu.3
    midex
    wph
    @3
    cB
    cA
    vy
    cv
    #
    cS
    cfv
    #
    cfv
    #
    wceq
    #
    wa
    #
    @0
    @5
    wceq
    #
    wi
    #
    vy
    cP
    wral
    vx
    cP
    wral
    @4
    wph
    @11
    vx
    vy
    cP
    cP
    wph
    @0
    cP
    wcel
    #
    @5
    cP
    wcel
    #
    wa
    #
    wa
    #
    @9
    @10
    @15
    @9
    wa
    #
    @0
    @5
    cP
    cS
    cG
    cI
    cL
    c.mi
    cA
    cB
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    mideu.s
    wph
    cG
    cstrkg
    wcel
    @14
    @9
    colperpex.g
    ad2antrr
    wph
    @12
    @13
    @9
    simplrl
    wph
    @12
    @13
    @9
    simplrr
    wph
    cA
    cP
    wcel
    @14
    @9
    mideu.1
    ad2antrr
    wph
    cB
    cP
    wcel
    @14
    @9
    mideu.2
    ad2antrr
    @16
    cB
    @2
    @15
    @3
    @8
    simprl
    eqcomd
    @16
    cB
    @7
    @15
    @3
    @8
    simprr
    eqcomd
    miduniq
    ex
    ralrimivva
    @3
    @8
    vx
    vy
    cP
    @10
    @2
    @7
    cB
    @10
    cA
    @1
    @6
    @0
    @5
    cS
    fveq2
    fveq1d
    eqeq2d
    rmo4
    sylibr
    @3
    vx
    cP
    reu5
    sylanbrc
end
