include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "corvc.mm"
include "co.mm"
include "crab.mm"
include "wfun.mm"
include "crn.mm"
include "wss.mm"
include "wceq.mm"
include "csigagen.mm"
include "cfv.mm"
include "ctop.mm"
include "sgsiga.mm"
include "isanmbfm.mm"
include "mbfmfun.mm"
include "wf.mm"
include "mbfmf.mm"
include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "unisg.mm"
include "3syl.mm"
include "feq3d.mm"
include "mpbid.mm"
include "frn.mm"
include "syl.mm"
include "fimacnvinrn2.mm"
include "syl2anc.mm"
include "cmbfm.mm"
include "orvcval.mm"
include "dfrab2.mm"
include "a1i.mm"
include "imaeq2d.mm"
include "3eqtr4d.mm"

theorem orvcval4
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let cJ: class J
  let cV: class V
  let cX: class X
  assume orvccel.1: |- ( ph -> S e. U. ran sigAlgebra )
  assume orvccel.2: |- ( ph -> J e. Top )
  assume orvccel.3: |- ( ph -> X e. ( S MblFnM ( sigaGen ` J ) ) )
  assume orvccel.4: |- ( ph -> A e. V )

  disjoint A y
  disjoint R y
  disjoint X y
  disjoint J y
  assert |- ( ph -> ( X oRVC R A ) = ( `' X " { y e. U. J | y R A } ) )

  proof
    wph
    cX
    ccnv
    #
    vy
    cv
    cA
    cR
    wbr
    #
    vy
    cab
    #
    cima
    #
    @0
    @2
    cJ
    cuni
    #
    cin
    #
    cima
    #
    cX
    cA
    cR
    corvc
    co
    @0
    @1
    vy
    @4
    crab
    #
    cima
    wph
    cX
    wfun
    cX
    crn
    @4
    wss
    #
    @3
    @6
    wceq
    wph
    cX
    wph
    cS
    cJ
    csigagen
    cfv
    #
    cX
    orvccel.1
    wph
    cJ
    ctop
    orvccel.2
    sgsiga
    #
    orvccel.3
    isanmbfm
    mbfmfun
    #
    wph
    cS
    cuni
    #
    @4
    cX
    wf
    #
    @8
    wph
    @12
    @9
    cuni
    #
    cX
    wf
    @13
    wph
    cS
    @9
    cX
    orvccel.1
    @10
    orvccel.3
    mbfmf
    wph
    @14
    @4
    cX
    @12
    wph
    cJ
    ctop
    wcel
    cJ
    cvv
    wcel
    @14
    @4
    wceq
    orvccel.2
    cJ
    ctop
    elex
    cJ
    cvv
    unisg
    3syl
    feq3d
    mpbid
    @12
    @4
    cX
    frn
    syl
    @2
    @4
    cX
    fimacnvinrn2
    syl2anc
    wph
    vy
    cA
    cR
    cS
    @9
    cmbfm
    co
    cV
    cX
    @11
    orvccel.3
    orvccel.4
    orvcval
    wph
    @7
    @5
    @0
    @7
    @5
    wceq
    wph
    @1
    vy
    @4
    dfrab2
    a1i
    imaeq2d
    3eqtr4d
end
