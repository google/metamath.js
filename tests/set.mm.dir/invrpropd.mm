include "cmgp.mm"
include "cfv.mm"
include "cui.mm"
include "cress.mm"
include "co.mm"
include "cminusg.mm"
include "cinvr.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "unitgrpbas.mm"
include "a1i.mm"
include "unitpropd.mm"
include "syl6eq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmulr.mm"
include "cplusg.mm"
include "unitss.mm"
include "syl5sseqr.mm"
include "sselda.mm"
include "anim12dan.mm"
include "syldan.mm"
include "cvv.mm"
include "fvex.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "oveqi.mm"
include "3eqtr3g.mm"
include "grpinvpropd.mm"
include "invrfval.mm"
include "3eqtr4g.mm"

theorem invrpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vz: setvar z
  assume rngidpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume rngidpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume rngidpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint x z
  disjoint y z
  disjoint K z
  disjoint L z
  disjoint ph z
  assert |- ( ph -> ( invr ` K ) = ( invr ` L ) )

  proof
    wph
    cK
    cmgp
    cfv
    #
    cK
    cui
    cfv
    #
    cress
    co
    #
    cminusg
    cfv
    cL
    cmgp
    cfv
    #
    cL
    cui
    cfv
    #
    cress
    co
    #
    cminusg
    cfv
    cK
    cinvr
    cfv
    #
    cL
    cinvr
    cfv
    #
    wph
    vx
    vy
    @1
    @2
    @5
    @1
    @2
    cbs
    cfv
    wceq
    wph
    cK
    @1
    @2
    @1
    eqid
    #
    @2
    eqid
    #
    unitgrpbas
    a1i
    wph
    @1
    @4
    @5
    cbs
    cfv
    wph
    vx
    vy
    cB
    cK
    cL
    rngidpropd.1
    rngidpropd.2
    rngidpropd.3
    unitpropd
    cL
    @4
    @5
    @4
    eqid
    #
    @5
    eqid
    #
    unitgrpbas
    syl6eq
    wph
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    wa
    #
    wa
    @12
    @14
    cK
    cmulr
    cfv
    #
    co
    #
    @12
    @14
    cL
    cmulr
    cfv
    #
    co
    #
    @12
    @14
    @2
    cplusg
    cfv
    #
    co
    @12
    @14
    @5
    cplusg
    cfv
    #
    co
    wph
    @16
    @12
    cB
    wcel
    #
    @14
    cB
    wcel
    #
    wa
    @18
    @20
    wceq
    wph
    @13
    @23
    @15
    @24
    wph
    @1
    cB
    @12
    wph
    cK
    cbs
    cfv
    #
    @1
    cB
    @25
    cK
    @1
    @25
    eqid
    @8
    unitss
    rngidpropd.1
    syl5sseqr
    #
    sselda
    wph
    @1
    cB
    @14
    @26
    sselda
    anim12dan
    rngidpropd.3
    syldan
    @17
    @21
    @12
    @14
    @1
    cvv
    wcel
    @17
    @21
    wceq
    cK
    cui
    fvex
    @1
    @17
    @0
    @2
    cvv
    @9
    cK
    @17
    @0
    @0
    eqid
    @17
    eqid
    mgpplusg
    ressplusg
    ax-mp
    oveqi
    @19
    @22
    @12
    @14
    @4
    cvv
    wcel
    @19
    @22
    wceq
    cL
    cui
    fvex
    @4
    @19
    @3
    @5
    cvv
    @11
    cL
    @19
    @3
    @3
    eqid
    @19
    eqid
    mgpplusg
    ressplusg
    ax-mp
    oveqi
    3eqtr3g
    grpinvpropd
    cK
    @1
    @2
    @6
    @8
    @9
    @6
    eqid
    invrfval
    cL
    @4
    @5
    @7
    @10
    @11
    @7
    eqid
    invrfval
    3eqtr4g
end
