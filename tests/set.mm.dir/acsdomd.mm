include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "wf.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "acsmap2d.mm"
include "simprr.mm"
include "cvv.mm"
include "wss.mm"
include "simprl.mm"
include "inss2.mm"
include "fss.mm"
include "sylancl.mm"
include "wcel.mm"
include "wn.mm"
include "acsinfd.mm"
include "adantr.mm"
include "cacs.mm"
include "cfv.mm"
include "elfvexd.mm"
include "ssexd.mm"
include "unirnfdomd.mm"
include "eqbrtrd.mm"
include "exlimddv.mm"

theorem acsdomd
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


  assert |- ( ph -> S ~<_ T )

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
    cS
    cT
    cdom
    wbr
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
    cS
    @4
    cT
    cdom
    wph
    @3
    @5
    simprr
    @7
    cT
    @2
    cvv
    @7
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
    simprl
    @0
    cfn
    inss2
    cT
    @1
    cfn
    @2
    fss
    sylancl
    wph
    cT
    cfn
    wcel
    wn
    @6
    wph
    cA
    cS
    cT
    cI
    cN
    cX
    acsmap2d.1
    acsmap2d.2
    acsmap2d.3
    acsmap2d.4
    acsmap2d.5
    acsmap2d.6
    acsinfd.7
    acsinfd
    adantr
    @7
    cT
    cX
    cvv
    @7
    cA
    cacs
    cX
    wph
    cA
    cX
    cacs
    cfv
    wcel
    @6
    acsmap2d.1
    adantr
    elfvexd
    wph
    cT
    cX
    wss
    @6
    acsmap2d.5
    adantr
    ssexd
    unirnfdomd
    eqbrtrd
    exlimddv
end
