include "wcel.mm"
include "cfbas.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "cfm.mm"
include "co.mm"
include "cv.mm"
include "wss.mm"
include "cima.mm"
include "wrex.mm"
include "wa.mm"
include "elfm2.mm"
include "wb.mm"
include "cfil.mm"
include "cfg.mm"
include "fgcl.mm"
include "syl5eqel.mm"
include "filfbas.mm"
include "syl.mm"
include "elfm.mm"
include "syl3an2.mm"
include "bitr4d.mm"
include "eqrdv.mm"

theorem fmfg
  let cB: class B
  let cC: class C
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume elfm2.l: |- L = ( Y filGen B )


  assert |- ( ( X e. C /\ B e. ( fBas ` Y ) /\ F : Y --> X ) -> ( ( X FilMap F ) ` B ) = ( ( X FilMap F ) ` L ) )

  proof
    cX
    cC
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
    vx
    cB
    cX
    cF
    cfm
    co
    #
    cfv
    #
    cL
    @5
    cfv
    #
    @4
    vx
    cv
    #
    @6
    wcel
    @8
    cX
    wss
    cF
    vs
    cv
    cima
    @8
    wss
    vs
    cL
    wrex
    wa
    #
    @8
    @7
    wcel
    #
    vs
    @8
    cB
    cC
    cF
    cL
    cX
    cY
    elfm2.l
    elfm2
    @2
    @0
    cL
    @1
    wcel
    #
    @3
    @10
    @9
    wb
    @2
    cL
    cY
    cfil
    cfv
    #
    wcel
    @11
    @2
    cL
    cY
    cB
    cfg
    co
    @12
    elfm2.l
    cB
    cY
    fgcl
    syl5eqel
    cL
    cY
    filfbas
    syl
    vs
    @8
    cL
    cC
    cF
    cX
    cY
    elfm
    syl3an2
    bitr4d
    eqrdv
end
