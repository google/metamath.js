include "csca.mm"
include "cfv.mm"
include "eqid.mm"
include "cbs.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "wceq.mm"
include "eqtr3d.mm"
include "adantr.mm"
include "oveqd.mm"
include "cmulr.mm"
include "lmodprop2d.mm"

theorem lmodpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let cF: class F
  let cK: class K
  let cL: class L
  assume lmodpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume lmodpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume lmodpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume lmodpropd.4: |- ( ph -> F = ( Scalar ` K ) )
  assume lmodpropd.5: |- ( ph -> F = ( Scalar ` L ) )
  assume lmodpropd.6: |- P = ( Base ` F )
  assume lmodpropd.7: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` K ) y ) = ( x ( .s ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( K e. LMod <-> L e. LMod ) )

  proof
    wph
    vx
    vy
    cB
    cP
    cK
    csca
    cfv
    #
    cL
    csca
    cfv
    #
    cK
    cL
    lmodpropd.1
    lmodpropd.2
    @0
    eqid
    @1
    eqid
    wph
    cP
    cF
    cbs
    cfv
    #
    @0
    cbs
    cfv
    lmodpropd.6
    wph
    cF
    @0
    cbs
    lmodpropd.4
    fveq2d
    syl5eq
    wph
    cP
    @2
    @1
    cbs
    cfv
    lmodpropd.6
    wph
    cF
    @1
    cbs
    lmodpropd.5
    fveq2d
    syl5eq
    lmodpropd.3
    wph
    vx
    cv
    #
    cP
    wcel
    vy
    cv
    #
    cP
    wcel
    wa
    #
    wa
    #
    @0
    cplusg
    cfv
    @1
    cplusg
    cfv
    @3
    @4
    @6
    @0
    @1
    cplusg
    wph
    @0
    @1
    wceq
    @5
    wph
    cF
    @0
    @1
    lmodpropd.4
    lmodpropd.5
    eqtr3d
    adantr
    #
    fveq2d
    oveqd
    @6
    @0
    cmulr
    cfv
    @1
    cmulr
    cfv
    @3
    @4
    @6
    @0
    @1
    cmulr
    @7
    fveq2d
    oveqd
    lmodpropd.7
    lmodprop2d
end
