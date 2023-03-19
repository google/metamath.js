include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "c0g.mm"
include "cds.mm"
include "co.mm"
include "cmpt.mm"
include "cnm.mm"
include "eqidd.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "oveqdr.mm"
include "grpidpropd.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "nmfval.mm"
include "3eqtr4g.mm"

theorem nmpropd
  let wph: wff ph
  let cK: class K
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  assume nmpropd.1: |- ( ph -> ( Base ` K ) = ( Base ` L ) )
  assume nmpropd.2: |- ( ph -> ( +g ` K ) = ( +g ` L ) )
  assume nmpropd.3: |- ( ph -> ( dist ` K ) = ( dist ` L ) )


  assert |- ( ph -> ( norm ` K ) = ( norm ` L ) )

  proof
    wph
    vx
    cK
    cbs
    cfv
    #
    vx
    cv
    #
    cK
    c0g
    cfv
    #
    cK
    cds
    cfv
    #
    co
    #
    cmpt
    vx
    cL
    cbs
    cfv
    #
    @1
    cL
    c0g
    cfv
    #
    cL
    cds
    cfv
    #
    co
    #
    cmpt
    cK
    cnm
    cfv
    #
    cL
    cnm
    cfv
    #
    wph
    vx
    @0
    @4
    @5
    @8
    nmpropd.1
    wph
    @1
    @1
    @2
    @6
    @3
    @7
    nmpropd.3
    wph
    @1
    eqidd
    wph
    vx
    vy
    @0
    cK
    cL
    wph
    @0
    eqidd
    nmpropd.1
    wph
    @1
    @0
    wcel
    vy
    cv
    @0
    wcel
    wa
    vx
    vy
    cK
    cplusg
    cfv
    cL
    cplusg
    cfv
    nmpropd.2
    oveqdr
    grpidpropd
    oveq123d
    mpteq12dv
    vx
    @3
    @9
    cK
    @0
    @2
    @9
    eqid
    @0
    eqid
    @2
    eqid
    @3
    eqid
    nmfval
    vx
    @7
    @10
    cL
    @5
    @6
    @10
    eqid
    @5
    eqid
    @6
    eqid
    @7
    eqid
    nmfval
    3eqtr4g
end
