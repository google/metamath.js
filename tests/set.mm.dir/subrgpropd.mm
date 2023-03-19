include "csubrg.mm"
include "cfv.mm"
include "crg.mm"
include "wcel.mm"
include "cv.mm"
include "cress.mm"
include "co.mm"
include "wa.mm"
include "cbs.mm"
include "wss.mm"
include "cur.mm"
include "ringpropd.mm"
include "cin.mm"
include "ineq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "vex.mm"
include "eqid.mm"
include "ressbas.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "cplusg.mm"
include "inss2.mm"
include "sseli.mm"
include "anim12i.mm"
include "ressplusg.mm"
include "oveqi.mm"
include "3eqtr3g.mm"
include "sylan2.mm"
include "cmulr.mm"
include "ressmulr.mm"
include "anbi12d.mm"
include "eqtr3d.mm"
include "sseq2d.mm"
include "rngidpropd.mm"
include "eleq1d.mm"
include "issubrg.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem subrgpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vs: setvar s
  assume subrgpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume subrgpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume subrgpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume subrgpropd.4: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint L x
  disjoint L y
  disjoint s x
  disjoint s y
  disjoint B s
  disjoint K s
  disjoint ph s
  disjoint L s
  assert |- ( ph -> ( SubRing ` K ) = ( SubRing ` L ) )

  proof
    wph
    vs
    cK
    csubrg
    cfv
    #
    cL
    csubrg
    cfv
    #
    wph
    cK
    crg
    wcel
    #
    cK
    vs
    cv
    #
    cress
    co
    #
    crg
    wcel
    #
    wa
    #
    @3
    cK
    cbs
    cfv
    #
    wss
    #
    cK
    cur
    cfv
    #
    @3
    wcel
    #
    wa
    #
    wa
    cL
    crg
    wcel
    #
    cL
    @3
    cress
    co
    #
    crg
    wcel
    #
    wa
    #
    @3
    cL
    cbs
    cfv
    #
    wss
    #
    cL
    cur
    cfv
    #
    @3
    wcel
    #
    wa
    #
    wa
    @3
    @0
    wcel
    @3
    @1
    wcel
    wph
    @6
    @15
    @11
    @20
    wph
    @2
    @12
    @5
    @14
    wph
    vx
    vy
    cB
    cK
    cL
    subrgpropd.1
    subrgpropd.2
    subrgpropd.3
    subrgpropd.4
    ringpropd
    wph
    vx
    vy
    @3
    cB
    cin
    #
    @4
    @13
    wph
    @21
    @3
    @7
    cin
    #
    @4
    cbs
    cfv
    #
    wph
    cB
    @7
    @3
    subrgpropd.1
    ineq2d
    @3
    cvv
    wcel
    #
    @22
    @23
    wceq
    vs
    vex
    #
    @3
    @7
    @4
    cvv
    cK
    @4
    eqid
    #
    @7
    eqid
    #
    ressbas
    ax-mp
    syl6eq
    wph
    @21
    @3
    @16
    cin
    #
    @13
    cbs
    cfv
    #
    wph
    cB
    @16
    @3
    subrgpropd.2
    ineq2d
    @24
    @28
    @29
    wceq
    @25
    @3
    @16
    @13
    cvv
    cL
    @13
    eqid
    #
    @16
    eqid
    #
    ressbas
    ax-mp
    syl6eq
    vx
    cv
    #
    @21
    wcel
    #
    vy
    cv
    #
    @21
    wcel
    #
    wa
    #
    wph
    @32
    cB
    wcel
    #
    @34
    cB
    wcel
    #
    wa
    #
    @32
    @34
    @4
    cplusg
    cfv
    #
    co
    #
    @32
    @34
    @13
    cplusg
    cfv
    #
    co
    #
    wceq
    @33
    @37
    @35
    @38
    @21
    cB
    @32
    @3
    cB
    inss2
    #
    sseli
    @21
    cB
    @34
    @44
    sseli
    anim12i
    #
    wph
    @39
    wa
    #
    @32
    @34
    cK
    cplusg
    cfv
    #
    co
    @32
    @34
    cL
    cplusg
    cfv
    #
    co
    @41
    @43
    subrgpropd.3
    @47
    @40
    @32
    @34
    @24
    @47
    @40
    wceq
    @25
    @3
    @47
    cK
    @4
    cvv
    @26
    @47
    eqid
    ressplusg
    ax-mp
    oveqi
    @48
    @42
    @32
    @34
    @24
    @48
    @42
    wceq
    @25
    @3
    @48
    cL
    @13
    cvv
    @30
    @48
    eqid
    ressplusg
    ax-mp
    oveqi
    3eqtr3g
    sylan2
    @36
    wph
    @39
    @32
    @34
    @4
    cmulr
    cfv
    #
    co
    #
    @32
    @34
    @13
    cmulr
    cfv
    #
    co
    #
    wceq
    @45
    @46
    @32
    @34
    cK
    cmulr
    cfv
    #
    co
    @32
    @34
    cL
    cmulr
    cfv
    #
    co
    @50
    @52
    subrgpropd.4
    @53
    @49
    @32
    @34
    @24
    @53
    @49
    wceq
    @25
    @3
    cK
    @4
    @53
    cvv
    @26
    @53
    eqid
    ressmulr
    ax-mp
    oveqi
    @54
    @51
    @32
    @34
    @24
    @54
    @51
    wceq
    @25
    @3
    cL
    @13
    @54
    cvv
    @30
    @54
    eqid
    ressmulr
    ax-mp
    oveqi
    3eqtr3g
    sylan2
    ringpropd
    anbi12d
    wph
    @8
    @17
    @10
    @19
    wph
    @7
    @16
    @3
    wph
    cB
    @7
    @16
    subrgpropd.1
    subrgpropd.2
    eqtr3d
    sseq2d
    wph
    @9
    @18
    @3
    wph
    vx
    vy
    cB
    cK
    cL
    subrgpropd.1
    subrgpropd.2
    subrgpropd.4
    rngidpropd
    eleq1d
    anbi12d
    anbi12d
    @3
    @7
    cK
    @9
    @27
    @9
    eqid
    issubrg
    @3
    @16
    cL
    @18
    @31
    @18
    eqid
    issubrg
    3bitr4g
    eqrdv
end
