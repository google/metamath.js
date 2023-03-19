include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "crio.mm"
include "cmpt.mm"
include "cminusg.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "grpidpropd.mm"
include "adantr.mm"
include "eqeq12d.mm"
include "anass1rs.mm"
include "riotabidva.mm"
include "mpteq2dva.mm"
include "riotaeqdv.mm"
include "mpteq12dv.mm"
include "3eqtr3d.mm"
include "eqid.mm"
include "grpinvfval.mm"
include "3eqtr4g.mm"

theorem grpinvpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  assume grpinvpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume grpinvpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume grpinvpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( invg ` K ) = ( invg ` L ) )

  proof
    wph
    vy
    cK
    cbs
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    cK
    cplusg
    cfv
    #
    co
    #
    cK
    c0g
    cfv
    #
    wceq
    #
    vx
    @0
    crio
    #
    cmpt
    #
    vy
    cL
    cbs
    cfv
    #
    @1
    @2
    cL
    cplusg
    cfv
    #
    co
    #
    cL
    c0g
    cfv
    #
    wceq
    #
    vx
    @9
    crio
    #
    cmpt
    #
    cK
    cminusg
    cfv
    #
    cL
    cminusg
    cfv
    #
    wph
    vy
    cB
    @6
    vx
    cB
    crio
    #
    cmpt
    vy
    cB
    @13
    vx
    cB
    crio
    #
    cmpt
    @8
    @15
    wph
    vy
    cB
    @18
    @19
    wph
    @2
    cB
    wcel
    #
    wa
    @6
    @13
    vx
    cB
    wph
    @1
    cB
    wcel
    #
    @20
    @6
    @13
    wb
    wph
    @21
    @20
    wa
    #
    wa
    @4
    @11
    @5
    @12
    grpinvpropd.3
    wph
    @5
    @12
    wceq
    @22
    wph
    vx
    vy
    cB
    cK
    cL
    grpinvpropd.1
    grpinvpropd.2
    grpinvpropd.3
    grpidpropd
    adantr
    eqeq12d
    anass1rs
    riotabidva
    mpteq2dva
    wph
    vy
    cB
    @18
    @0
    @7
    grpinvpropd.1
    wph
    @6
    vx
    cB
    @0
    grpinvpropd.1
    riotaeqdv
    mpteq12dv
    wph
    vy
    cB
    @19
    @9
    @14
    grpinvpropd.2
    wph
    @13
    vx
    cB
    @9
    grpinvpropd.2
    riotaeqdv
    mpteq12dv
    3eqtr3d
    vy
    vx
    @0
    @3
    cK
    @16
    @5
    @0
    eqid
    @3
    eqid
    @5
    eqid
    @16
    eqid
    grpinvfval
    vy
    vx
    @9
    @10
    cL
    @17
    @12
    @9
    eqid
    @10
    eqid
    @12
    eqid
    @17
    eqid
    grpinvfval
    3eqtr4g
end
