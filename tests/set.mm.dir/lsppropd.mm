include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "clss.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "clspn.mm"
include "eqtr3d.mm"
include "pweqd.mm"
include "wceq.mm"
include "lsspropd.mm"
include "rabeq.mm"
include "syl.mm"
include "inteqd.mm"
include "mpteq12dv.mm"
include "cvv.mm"
include "wcel.mm"
include "eqid.mm"
include "lspfval.mm"
include "3eqtr4d.mm"

theorem lsppropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let cK: class K
  let cL: class L
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let vs: setvar s
  let vt: setvar t
  assume lsspropd.b1: |- ( ph -> B = ( Base ` K ) )
  assume lsspropd.b2: |- ( ph -> B = ( Base ` L ) )
  assume lsspropd.w: |- ( ph -> B C_ W )
  assume lsspropd.p: |- ( ( ph /\ ( x e. W /\ y e. W ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume lsspropd.s1: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` K ) y ) e. W )
  assume lsspropd.s2: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` K ) y ) = ( x ( .s ` L ) y ) )
  assume lsspropd.p1: |- ( ph -> P = ( Base ` ( Scalar ` K ) ) )
  assume lsspropd.p2: |- ( ph -> P = ( Base ` ( Scalar ` L ) ) )
  assume lsspropd.v1: |- ( ph -> K e. _V )
  assume lsspropd.v2: |- ( ph -> L e. _V )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint W x
  disjoint W y
  disjoint L x
  disjoint L y
  disjoint P x
  disjoint P y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint B a
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint a s
  disjoint a t
  disjoint K a
  disjoint b s
  disjoint b t
  disjoint K b
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint K s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint K t
  disjoint K z
  disjoint a ph
  disjoint b ph
  disjoint ph s
  disjoint ph z
  disjoint L a
  disjoint L b
  disjoint L s
  disjoint L t
  disjoint L z
  disjoint P a
  disjoint P b
  disjoint P z
  assert |- ( ph -> ( LSpan ` K ) = ( LSpan ` L ) )

  proof
    wph
    vs
    cK
    cbs
    cfv
    #
    cpw
    #
    vs
    cv
    vt
    cv
    wss
    #
    vt
    cK
    clss
    cfv
    #
    crab
    #
    cint
    #
    cmpt
    #
    vs
    cL
    cbs
    cfv
    #
    cpw
    #
    @2
    vt
    cL
    clss
    cfv
    #
    crab
    #
    cint
    #
    cmpt
    #
    cK
    clspn
    cfv
    #
    cL
    clspn
    cfv
    #
    wph
    vs
    @1
    @5
    @8
    @11
    wph
    @0
    @7
    wph
    cB
    @0
    @7
    lsspropd.b1
    lsspropd.b2
    eqtr3d
    pweqd
    wph
    @4
    @10
    wph
    @3
    @9
    wceq
    @4
    @10
    wceq
    wph
    vx
    vy
    cB
    cP
    cK
    cL
    cW
    lsspropd.b1
    lsspropd.b2
    lsspropd.w
    lsspropd.p
    lsspropd.s1
    lsspropd.s2
    lsspropd.p1
    lsspropd.p2
    lsspropd
    @2
    vt
    @3
    @9
    rabeq
    syl
    inteqd
    mpteq12dv
    wph
    cK
    cvv
    wcel
    @13
    @6
    wceq
    lsspropd.v1
    vt
    @3
    @13
    @0
    cK
    cvv
    vs
    @0
    eqid
    @3
    eqid
    @13
    eqid
    lspfval
    syl
    wph
    cL
    cvv
    wcel
    @14
    @12
    wceq
    lsspropd.v2
    vt
    @9
    @14
    @7
    cL
    cvv
    vs
    @7
    eqid
    @9
    eqid
    @14
    eqid
    lspfval
    syl
    3eqtr4d
end
