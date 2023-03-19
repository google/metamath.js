include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wa.mm"
include "cflf.mm"
include "co.mm"
include "cuni.mm"
include "cmap.mm"
include "cv.mm"
include "cfm.mm"
include "cflim.mm"
include "cmpt.mm"
include "ctop.mm"
include "crn.mm"
include "wceq.mm"
include "topontop.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "unieq.mm"
include "oveqan12d.mm"
include "simpl.mm"
include "adantr.mm"
include "oveq1d.mm"
include "simpr.mm"
include "fveq12d.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "df-flf.mm"
include "ovex.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "syl2an.mm"
include "toponuni.mm"
include "eqcomd.mm"
include "filunibas.mm"
include "fveq1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem flffval
  let vf: setvar f
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cF: class F

  disjoint J f
  disjoint X f
  disjoint Y f
  disjoint L f
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint F f
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint L x
  disjoint L y
  assert |- ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) ) -> ( J fLimf L ) = ( f e. ( X ^m Y ) |-> ( J fLim ( ( X FilMap f ) ` L ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cL
    cY
    cfil
    cfv
    #
    wcel
    #
    wa
    #
    cJ
    cL
    cflf
    co
    #
    vf
    cJ
    cuni
    #
    cL
    cuni
    #
    cmap
    co
    #
    cJ
    cL
    @5
    vf
    cv
    #
    cfm
    co
    #
    cfv
    #
    cflim
    co
    #
    cmpt
    #
    vf
    cX
    cY
    cmap
    co
    #
    cJ
    cL
    cX
    @8
    cfm
    co
    #
    cfv
    #
    cflim
    co
    #
    cmpt
    @0
    cJ
    ctop
    wcel
    cL
    cfil
    crn
    cuni
    #
    wcel
    @4
    @12
    wceq
    @2
    cX
    cJ
    topontop
    @1
    @17
    cL
    cfil
    cY
    fvssunirn
    sseli
    vx
    vy
    cJ
    cL
    ctop
    @17
    vf
    vx
    cv
    #
    cuni
    #
    vy
    cv
    #
    cuni
    #
    cmap
    co
    #
    @18
    @20
    @19
    @8
    cfm
    co
    #
    cfv
    #
    cflim
    co
    #
    cmpt
    @12
    cflf
    @18
    cJ
    wceq
    #
    @20
    cL
    wceq
    #
    wa
    #
    vf
    @22
    @25
    @7
    @11
    @26
    @27
    @19
    @5
    @21
    @6
    cmap
    @18
    cJ
    unieq
    #
    @20
    cL
    unieq
    oveqan12d
    @28
    @18
    cJ
    @24
    @10
    cflim
    @26
    @27
    simpl
    @28
    @20
    cL
    @23
    @9
    @28
    @19
    @5
    @8
    cfm
    @26
    @19
    @5
    wceq
    @27
    @29
    adantr
    oveq1d
    @26
    @27
    simpr
    fveq12d
    oveq12d
    mpteq12dv
    vx
    vy
    vf
    df-flf
    vf
    @7
    @11
    @5
    @6
    cmap
    ovex
    mptex
    ovmpt2a
    syl2an
    @3
    vf
    @7
    @11
    @13
    @16
    @0
    @2
    @5
    cX
    @6
    cY
    cmap
    @0
    cX
    @5
    cX
    cJ
    toponuni
    eqcomd
    #
    cL
    cY
    filunibas
    oveqan12d
    @3
    @10
    @15
    cJ
    cflim
    @3
    cL
    @9
    @14
    @3
    @5
    cX
    @8
    cfm
    @0
    @5
    cX
    wceq
    @2
    @30
    adantr
    oveq1d
    fveq1d
    oveq2d
    mpteq12dv
    eqtrd
end
