include "zring.mm"
include "crh.mm"
include "co.mm"
include "cuni.mm"
include "czrh.mm"
include "cfv.mm"
include "cbs.mm"
include "eqidd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cmulr.mm"
include "rhmpropd.mm"
include "unieqd.mm"
include "eqid.mm"
include "zrhval.mm"
include "3eqtr4g.mm"

theorem zrhpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  assume zrhpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume zrhpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume zrhpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume zrhpropd.4: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( ZRHom ` K ) = ( ZRHom ` L ) )

  proof
    wph
    zring
    cK
    crh
    co
    #
    cuni
    zring
    cL
    crh
    co
    #
    cuni
    cK
    czrh
    cfv
    #
    cL
    czrh
    cfv
    #
    wph
    @0
    @1
    wph
    vx
    vy
    zring
    cbs
    cfv
    #
    cB
    zring
    cK
    zring
    cL
    wph
    @4
    eqidd
    #
    zrhpropd.1
    @5
    zrhpropd.2
    wph
    vx
    cv
    #
    @4
    wcel
    vy
    cv
    #
    @4
    wcel
    wa
    wa
    #
    @6
    @7
    zring
    cplusg
    cfv
    co
    eqidd
    zrhpropd.3
    @8
    @6
    @7
    zring
    cmulr
    cfv
    co
    eqidd
    zrhpropd.4
    rhmpropd
    unieqd
    cK
    @2
    @2
    eqid
    zrhval
    cL
    @3
    @3
    eqid
    zrhval
    3eqtr4g
end
