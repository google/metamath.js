include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cur.mm"
include "cvsca.mm"
include "co.mm"
include "cmpt.mm"
include "cascl.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "oveqrspc2v.mm"
include "anassrs.mm"
include "mpidan.mm"
include "oveq2d.mm"
include "adantr.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "mpteq1d.mm"
include "3eqtr3d.mm"
include "eqid.mm"
include "asclfval.mm"
include "3eqtr4g.mm"

theorem asclpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cW: class W
  let vz: setvar z
  assume asclpropd.f: |- F = ( Scalar ` K )
  assume asclpropd.g: |- G = ( Scalar ` L )
  assume asclpropd.1: |- ( ph -> P = ( Base ` F ) )
  assume asclpropd.2: |- ( ph -> P = ( Base ` G ) )
  assume asclpropd.3: |- ( ( ph /\ ( x e. P /\ y e. W ) ) -> ( x ( .s ` K ) y ) = ( x ( .s ` L ) y ) )
  assume asclpropd.4: |- ( ph -> ( 1r ` K ) = ( 1r ` L ) )
  assume asclpropd.5: |- ( ph -> ( 1r ` K ) e. W )

  disjoint x y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  disjoint W x
  disjoint W y
  disjoint x z
  disjoint y z
  disjoint K z
  disjoint L z
  disjoint P z
  disjoint ph z
  disjoint F z
  disjoint G z
  assert |- ( ph -> ( algSc ` K ) = ( algSc ` L ) )

  proof
    wph
    vz
    cF
    cbs
    cfv
    #
    vz
    cv
    #
    cK
    cur
    cfv
    #
    cK
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    vz
    cG
    cbs
    cfv
    #
    @1
    cL
    cur
    cfv
    #
    cL
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cK
    cascl
    cfv
    #
    cL
    cascl
    cfv
    #
    wph
    vz
    cP
    @4
    cmpt
    vz
    cP
    @9
    cmpt
    @5
    @10
    wph
    vz
    cP
    @4
    @9
    wph
    @1
    cP
    wcel
    #
    wa
    @4
    @1
    @2
    @8
    co
    #
    @9
    wph
    @13
    @2
    cW
    wcel
    #
    @4
    @14
    wceq
    #
    asclpropd.5
    wph
    @13
    @15
    @16
    wph
    vx
    vy
    cP
    cW
    @3
    @8
    @1
    @2
    asclpropd.3
    oveqrspc2v
    anassrs
    mpidan
    wph
    @14
    @9
    wceq
    @13
    wph
    @2
    @7
    @1
    @8
    asclpropd.4
    oveq2d
    adantr
    eqtrd
    mpteq2dva
    wph
    vz
    cP
    @0
    @4
    asclpropd.1
    mpteq1d
    wph
    vz
    cP
    @6
    @9
    asclpropd.2
    mpteq1d
    3eqtr3d
    vz
    @11
    @3
    @2
    cF
    @0
    cK
    @11
    eqid
    asclpropd.f
    @0
    eqid
    @3
    eqid
    @2
    eqid
    asclfval
    vz
    @12
    @8
    @7
    cG
    @6
    cL
    @12
    eqid
    asclpropd.g
    @6
    eqid
    @8
    eqid
    @7
    eqid
    asclfval
    3eqtr4g
end
