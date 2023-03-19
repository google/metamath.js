include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "wf.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "wn.mm"
include "acsmap2d.mm"
include "simplrr.mm"
include "wss.mm"
include "simplrl.mm"
include "inss2.mm"
include "fss.mm"
include "sylancl.mm"
include "simpr.mm"
include "unirnffid.mm"
include "eqeltrd.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "exlimddv.mm"

theorem acsinfd
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cI: class I
  let cN: class N
  let cX: class X
  let vf: setvar f
  assume acsmap2d.1: |- ( ph -> A e. ( ACS ` X ) )
  assume acsmap2d.2: |- N = ( mrCls ` A )
  assume acsmap2d.3: |- I = ( mrInd ` A )
  assume acsmap2d.4: |- ( ph -> S e. I )
  assume acsmap2d.5: |- ( ph -> T C_ X )
  assume acsmap2d.6: |- ( ph -> ( N ` S ) = ( N ` T ) )
  assume acsinfd.7: |- ( ph -> -. S e. Fin )


  assert |- ( ph -> -. T e. Fin )

  proof
    wph
    cT
    cS
    cpw
    #
    cfn
    cin
    #
    vf
    cv
    #
    wf
    #
    cS
    @2
    crn
    cuni
    #
    wceq
    #
    wa
    #
    cT
    cfn
    wcel
    #
    wn
    vf
    wph
    cA
    cS
    cT
    vf
    cI
    cN
    cX
    acsmap2d.1
    acsmap2d.2
    acsmap2d.3
    acsmap2d.4
    acsmap2d.5
    acsmap2d.6
    acsmap2d
    wph
    @6
    wa
    #
    @7
    cS
    cfn
    wcel
    #
    @8
    @7
    wa
    #
    cS
    @4
    cfn
    wph
    @3
    @5
    @7
    simplrr
    @10
    cT
    @2
    @10
    @3
    @1
    cfn
    wss
    cT
    cfn
    @2
    wf
    wph
    @3
    @5
    @7
    simplrl
    @0
    cfn
    inss2
    cT
    @1
    cfn
    @2
    fss
    sylancl
    @8
    @7
    simpr
    unirnffid
    eqeltrd
    wph
    @9
    wn
    @6
    @7
    acsinfd.7
    ad2antrr
    pm2.65da
    exlimddv
end
