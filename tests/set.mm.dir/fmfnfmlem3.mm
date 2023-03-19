include "cv.mm"
include "cin.mm"
include "ccnv.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "wcel.mm"
include "wral.mm"
include "cfi.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cfil.mm"
include "filin.mm"
include "3expb.mm"
include "sylan.mm"
include "wf.mm"
include "wfun.mm"
include "ffun.mm"
include "funcnvcnv.mm"
include "imain.mm"
include "eqcomd.mm"
include "4syl.mm"
include "adantr.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ineq12.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "cbvrexv.mm"
include "anbi12i.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "reeanv.mm"
include "3bitr4i.mm"
include "inex1.mm"
include "3imtr4g.mm"
include "ralrimivv.mm"
include "mptexg.mm"
include "rnexg.mm"
include "inficl.mm"
include "mpbid.mm"

theorem fmfnfmlem3
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume fmfnfm.b: |- ( ph -> B e. ( fBas ` Y ) )
  assume fmfnfm.l: |- ( ph -> L e. ( Fil ` X ) )
  assume fmfnfm.f: |- ( ph -> F : Y --> X )
  assume fmfnfm.fm: |- ( ph -> ( ( X FilMap F ) ` B ) C_ L )

  disjoint B x
  disjoint F x
  disjoint L x
  disjoint ph x
  disjoint X x
  disjoint Y x
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F f
  disjoint F s
  disjoint F t
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint L f
  disjoint L s
  disjoint L t
  disjoint L w
  disjoint L y
  disjoint L z
  disjoint ph s
  disjoint ph t
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint X f
  disjoint X s
  disjoint X t
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y s
  disjoint Y t
  disjoint Y w
  disjoint Y z
  assert |- ( ph -> ( fi ` ran ( x e. L |-> ( `' F " x ) ) ) = ran ( x e. L |-> ( `' F " x ) ) )

  proof
    wph
    vs
    cv
    #
    vt
    cv
    #
    cin
    #
    vx
    cL
    cF
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    wcel
    #
    vt
    @7
    wral
    vs
    @7
    wral
    #
    @7
    cfi
    cfv
    @7
    wceq
    #
    wph
    @8
    vs
    vt
    @7
    @7
    wph
    @0
    @3
    vy
    cv
    #
    cima
    #
    wceq
    #
    @1
    @3
    vz
    cv
    #
    cima
    #
    wceq
    #
    wa
    #
    vz
    cL
    wrex
    vy
    cL
    wrex
    #
    @2
    @5
    wceq
    #
    vx
    cL
    wrex
    #
    @0
    @7
    wcel
    #
    @1
    @7
    wcel
    #
    wa
    #
    @8
    wph
    @17
    @20
    vy
    vz
    cL
    cL
    wph
    @11
    cL
    wcel
    #
    @14
    cL
    wcel
    #
    wa
    #
    wa
    #
    @20
    @17
    @12
    @15
    cin
    #
    @5
    wceq
    #
    vx
    cL
    wrex
    #
    @27
    @11
    @14
    cin
    #
    cL
    wcel
    #
    @28
    @3
    @31
    cima
    #
    wceq
    #
    @30
    wph
    cL
    cX
    cfil
    cfv
    #
    wcel
    #
    @26
    @32
    fmfnfm.l
    @36
    @24
    @25
    @32
    @11
    @14
    cL
    cX
    filin
    3expb
    sylan
    wph
    @34
    @26
    wph
    cY
    cX
    cF
    wf
    cF
    wfun
    @3
    ccnv
    wfun
    #
    @34
    fmfnfm.f
    cY
    cX
    cF
    ffun
    cF
    funcnvcnv
    @37
    @33
    @28
    @11
    @14
    @3
    imain
    eqcomd
    4syl
    adantr
    @29
    @34
    vx
    @31
    cL
    @4
    @31
    wceq
    @5
    @33
    @28
    @4
    @31
    @3
    imaeq2
    eqeq2d
    rspcev
    syl2anc
    @17
    @19
    @29
    vx
    cL
    @17
    @2
    @28
    @5
    @0
    @12
    @1
    @15
    ineq12
    eqeq1d
    rexbidv
    syl5ibrcom
    rexlimdvva
    @0
    @5
    wceq
    #
    vx
    cL
    wrex
    #
    @1
    @5
    wceq
    #
    vx
    cL
    wrex
    #
    wa
    @13
    vy
    cL
    wrex
    #
    @16
    vz
    cL
    wrex
    #
    wa
    @23
    @18
    @39
    @42
    @41
    @43
    @38
    @13
    vx
    vy
    cL
    @4
    @11
    wceq
    @5
    @12
    @0
    @4
    @11
    @3
    imaeq2
    eqeq2d
    cbvrexv
    @40
    @16
    vx
    vz
    cL
    @4
    @14
    wceq
    @5
    @15
    @1
    @4
    @14
    @3
    imaeq2
    eqeq2d
    cbvrexv
    anbi12i
    @21
    @39
    @22
    @41
    @0
    cvv
    wcel
    @21
    @39
    wb
    vs
    vex
    #
    vx
    cL
    @5
    @0
    @6
    cvv
    @6
    eqid
    #
    elrnmpt
    ax-mp
    @1
    cvv
    wcel
    @22
    @41
    wb
    vt
    vex
    vx
    cL
    @5
    @1
    @6
    cvv
    @45
    elrnmpt
    ax-mp
    anbi12i
    @13
    @16
    vy
    vz
    cL
    cL
    reeanv
    3bitr4i
    @2
    cvv
    wcel
    @8
    @20
    wb
    @0
    @1
    @44
    inex1
    vx
    cL
    @5
    @2
    @6
    cvv
    @45
    elrnmpt
    ax-mp
    3imtr4g
    ralrimivv
    wph
    @36
    @6
    cvv
    wcel
    @7
    cvv
    wcel
    @9
    @10
    wb
    fmfnfm.l
    vx
    cL
    @5
    @35
    mptexg
    @6
    cvv
    rnexg
    vs
    vt
    @7
    cvv
    inficl
    4syl
    mpbid
end
