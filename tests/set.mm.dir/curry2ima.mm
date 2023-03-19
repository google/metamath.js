include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "co.mm"
include "wfun.mm"
include "cdm.mm"
include "cvv.mm"
include "wf.mm"
include "simp1.mm"
include "dffn2.mm"
include "sylib.mm"
include "simp2.mm"
include "curry2f.mm"
include "syl2anc.mm"
include "ffun.mm"
include "syl.mm"
include "simp3.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "dfimafn.mm"
include "curry2val.mm"
include "3adant3.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "eqtrd.mm"

theorem curry2ima
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume curry2ima.1: |- G = ( F o. `' ( 1st |` ( _V X. { C } ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  assert |- ( ( F Fn ( A X. B ) /\ C e. B /\ D C_ A ) -> ( G " D ) = { y | E. x e. D y = ( x F C ) } )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    #
    cC
    cB
    wcel
    #
    cD
    cA
    wss
    #
    w3a
    #
    cG
    cD
    cima
    #
    vx
    cv
    #
    cG
    cfv
    #
    vy
    cv
    #
    wceq
    #
    vx
    cD
    wrex
    #
    vy
    cab
    #
    @8
    @6
    cC
    cF
    co
    #
    wceq
    #
    vx
    cD
    wrex
    #
    vy
    cab
    @4
    cG
    wfun
    #
    cD
    cG
    cdm
    #
    wss
    @5
    @11
    wceq
    @4
    cA
    cvv
    cG
    wf
    #
    @15
    @4
    @0
    cvv
    cF
    wf
    #
    @2
    @17
    @4
    @1
    @18
    @1
    @2
    @3
    simp1
    @0
    cF
    dffn2
    sylib
    @1
    @2
    @3
    simp2
    cA
    cB
    cC
    cvv
    cF
    cG
    curry2ima.1
    curry2f
    syl2anc
    #
    cA
    cvv
    cG
    ffun
    syl
    @4
    cD
    cA
    @16
    @1
    @2
    @3
    simp3
    @4
    @17
    @16
    cA
    wceq
    @19
    cA
    cvv
    cG
    fdm
    syl
    sseqtr4d
    vx
    vy
    cD
    cG
    dfimafn
    syl2anc
    @4
    @10
    @14
    vy
    @4
    @9
    @13
    vx
    cD
    @4
    @9
    @12
    @8
    wceq
    @13
    @4
    @7
    @12
    @8
    @1
    @2
    @7
    @12
    wceq
    @3
    cA
    cB
    cC
    @6
    cF
    cG
    curry2ima.1
    curry2val
    3adant3
    eqeq1d
    @12
    @8
    eqcom
    syl6bb
    rexbidv
    abbidv
    eqtrd
end
