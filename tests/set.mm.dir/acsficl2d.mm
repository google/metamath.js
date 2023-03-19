include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cima.mm"
include "cuni.mm"
include "cv.mm"
include "wrex.mm"
include "acsficld.mm"
include "eleq2d.mm"
include "cmre.mm"
include "wfun.mm"
include "wb.mm"
include "acsmred.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "funmpt.mm"
include "mrcfval.mm"
include "funeqd.mm"
include "mpbiri.mm"
include "eluniima.mm"
include "3syl.mm"
include "bitrd.mm"

theorem acsficl2d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cN: class N
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z
  assume acsficld.1: |- ( ph -> A e. ( ACS ` X ) )
  assume acsficld.2: |- N = ( mrCls ` A )
  assume acsficld.3: |- ( ph -> S C_ X )

  disjoint S x
  disjoint Y x
  disjoint N x
  disjoint A w
  disjoint A z
  disjoint w z
  disjoint X w
  disjoint X z
  disjoint N w
  disjoint N z
  assert |- ( ph -> ( Y e. ( N ` S ) <-> E. x e. ( ~P S i^i Fin ) Y e. ( N ` x ) ) )

  proof
    wph
    cY
    cS
    cN
    cfv
    #
    wcel
    cY
    cN
    cS
    cpw
    cfn
    cin
    #
    cima
    cuni
    #
    wcel
    #
    cY
    vx
    cv
    cN
    cfv
    wcel
    vx
    @1
    wrex
    #
    wph
    @0
    @2
    cY
    wph
    cA
    cS
    cN
    cX
    acsficld.1
    acsficld.2
    acsficld.3
    acsficld
    eleq2d
    wph
    cA
    cX
    cmre
    cfv
    wcel
    #
    cN
    wfun
    #
    @3
    @4
    wb
    wph
    cA
    cX
    acsficld.1
    acsmred
    @5
    @6
    vz
    cX
    cpw
    #
    vz
    cv
    vw
    cv
    wss
    vw
    cA
    crab
    cint
    #
    cmpt
    #
    wfun
    vz
    @7
    @8
    funmpt
    @5
    cN
    @9
    vz
    cA
    cN
    cX
    vw
    acsficld.2
    mrcfval
    funeqd
    mpbiri
    vx
    @1
    cY
    cN
    eluniima
    3syl
    bitrd
end
