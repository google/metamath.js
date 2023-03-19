include "wcel.mm"
include "cfbas.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "cfm.mm"
include "co.mm"
include "cv.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "cvv.mm"
include "cdm.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-fm.mm"
include "a1i.mm"
include "wa.mm"
include "dmeq.mm"
include "fveq2d.mm"
include "adantl.mm"
include "id.mm"
include "imaeq1.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "oveqan12d.mm"
include "mpteq12dv.mm"
include "fdm.mm"
include "mpteq1d.mm"
include "3ad2ant3.mm"
include "sylan9eqr.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "elfvdm.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "fex2.mm"
include "syl3anc.mm"
include "fvex.mm"
include "mptex.mm"
include "ovmpt2d.mm"
include "fveq1d.mm"
include "mpteq1.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqtrd.mm"

theorem fmval
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vf: setvar f
  let vx: setvar x

  disjoint B y
  disjoint F y
  disjoint X y
  disjoint Y y
  disjoint A y
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint x y
  disjoint B x
  disjoint F b
  disjoint F f
  disjoint F x
  disjoint X b
  disjoint X f
  disjoint X x
  disjoint Y b
  disjoint Y f
  disjoint Y x
  disjoint A f
  disjoint A x
  assert |- ( ( X e. A /\ B e. ( fBas ` Y ) /\ F : Y --> X ) -> ( ( X FilMap F ) ` B ) = ( X filGen ran ( y e. B |-> ( F " y ) ) ) )

  proof
    cX
    cA
    wcel
    #
    cB
    cY
    cfbas
    cfv
    #
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cB
    cX
    cF
    cfm
    co
    #
    cfv
    cB
    vb
    @1
    cX
    vy
    vb
    cv
    #
    cF
    vy
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cmpt
    #
    cfv
    #
    cX
    vy
    cB
    @8
    cmpt
    #
    crn
    #
    cfg
    co
    #
    @4
    cB
    @5
    @12
    @4
    vx
    vf
    cX
    cF
    cvv
    cvv
    vb
    vf
    cv
    #
    cdm
    #
    cfbas
    cfv
    #
    vx
    cv
    #
    vy
    @6
    @17
    @7
    cima
    #
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cmpt
    #
    @12
    cfm
    cvv
    cfm
    vx
    vf
    cvv
    cvv
    @25
    cmpt2
    wceq
    @4
    vx
    vb
    vy
    vf
    df-fm
    a1i
    @20
    cX
    wceq
    #
    @17
    cF
    wceq
    #
    wa
    #
    @4
    @25
    vb
    cF
    cdm
    #
    cfbas
    cfv
    #
    @11
    cmpt
    #
    @12
    @28
    vb
    @19
    @24
    @30
    @11
    @27
    @19
    @30
    wceq
    @26
    @27
    @18
    @29
    cfbas
    @17
    cF
    dmeq
    fveq2d
    adantl
    @26
    @27
    @20
    cX
    @23
    @10
    cfg
    @26
    id
    @27
    @22
    @9
    @27
    vy
    @6
    @21
    @8
    @17
    cF
    @7
    imaeq1
    mpteq2dv
    rneqd
    oveqan12d
    mpteq12dv
    @3
    @0
    @31
    @12
    wceq
    @2
    @3
    vb
    @30
    @1
    @11
    @3
    @29
    cY
    cfbas
    cY
    cX
    cF
    fdm
    fveq2d
    mpteq1d
    3ad2ant3
    sylan9eqr
    @0
    @2
    cX
    cvv
    wcel
    @3
    cX
    cA
    elex
    3ad2ant1
    @4
    @3
    cY
    cfbas
    cdm
    #
    wcel
    #
    @0
    cF
    cvv
    wcel
    @0
    @2
    @3
    simp3
    @2
    @0
    @33
    @3
    cB
    cY
    cfbas
    elfvdm
    3ad2ant2
    @0
    @2
    @3
    simp1
    cY
    cX
    cF
    @32
    cA
    fex2
    syl3anc
    @12
    cvv
    wcel
    @4
    vb
    @1
    @11
    cY
    cfbas
    fvex
    mptex
    a1i
    ovmpt2d
    fveq1d
    @2
    @0
    @13
    @16
    wceq
    @3
    vb
    cB
    @11
    @16
    @1
    @12
    @6
    cB
    wceq
    #
    @10
    @15
    cX
    cfg
    @34
    @9
    @14
    vy
    @6
    cB
    @8
    mpteq1
    rneqd
    oveq2d
    @12
    eqid
    cX
    @15
    cfg
    ovex
    fvmpt
    3ad2ant2
    eqtrd
end
