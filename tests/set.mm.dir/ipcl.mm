include "cphl.mm"
include "wcel.mm"
include "co.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cmpt.mm"
include "wf.mm"
include "crglmod.mm"
include "cfv.mm"
include "clmhm.mm"
include "eqid.mm"
include "phllmhm.mm"
include "cbs.mm"
include "rlmbas.mm"
include "eqtri.mm"
include "lmhmf.mm"
include "syl.mm"
include "fmpt.mm"
include "sylibr.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "stoic3.mm"
include "3com23.mm"

theorem ipcl
  let cA: class A
  let cB: class B
  let cF: class F
  let c.xi: class .,
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cG: class G
  let c.as: class .*
  let c.0: class .0.
  let c.x: class .x.
  let cZ: class Z
  assume phlsrng.f: |- F = ( Scalar ` W )
  assume phllmhm.h: |- ., = ( .i ` W )
  assume phllmhm.v: |- V = ( Base ` W )
  assume ipcl.f: |- K = ( Base ` F )


  assert |- ( ( W e. PreHil /\ A e. V /\ B e. V ) -> ( A ., B ) e. K )

  proof
    cW
    cphl
    wcel
    #
    cB
    cV
    wcel
    #
    cA
    cV
    wcel
    #
    cA
    cB
    c.xi
    co
    #
    cK
    wcel
    #
    @0
    @1
    vx
    cv
    #
    cB
    c.xi
    co
    #
    cK
    wcel
    #
    vx
    cV
    wral
    #
    @2
    @4
    @0
    @1
    wa
    #
    cV
    cK
    vx
    cV
    @6
    cmpt
    #
    wf
    #
    @8
    @9
    @10
    cW
    cF
    crglmod
    cfv
    #
    clmhm
    co
    wcel
    @11
    vx
    cB
    cF
    @10
    c.xi
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @10
    eqid
    #
    phllmhm
    cV
    cK
    cW
    @12
    @10
    phllmhm.v
    cK
    cF
    cbs
    cfv
    @12
    cbs
    cfv
    ipcl.f
    cF
    rlmbas
    eqtri
    lmhmf
    syl
    vx
    cV
    cK
    @6
    @10
    @13
    fmpt
    sylibr
    @7
    @4
    vx
    cA
    cV
    @5
    cA
    wceq
    @6
    @3
    cK
    @5
    cA
    cB
    c.xi
    oveq1
    eleq1d
    rspccva
    stoic3
    3com23
end
