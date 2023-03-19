include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "csm.mm"
include "co.mm"
include "cbr.mm"
include "cfv.mm"
include "cv.mm"
include "csp.mm"
include "cmpt.mm"
include "ccj.mm"
include "chft.mm"
include "wceq.mm"
include "hvmulcl.mm"
include "brafval.mm"
include "syl.mm"
include "cmul.mm"
include "wf.mm"
include "cjcl.mm"
include "brafn.mm"
include "hfmmval.mm"
include "syl2an.mm"
include "his5.mm"
include "3expa.mm"
include "an32s.mm"
include "braval.mm"
include "adantll.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "mpteq2dva.mm"

theorem brafnmul
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S
  let cT: class T


  assert |- ( ( A e. CC /\ B e. ~H ) -> ( bra ` ( A .h B ) ) = ( ( * ` A ) .fn ( bra ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    cB
    csm
    co
    #
    cbr
    cfv
    #
    vx
    chil
    vx
    cv
    #
    @3
    csp
    co
    #
    cmpt
    #
    cA
    ccj
    cfv
    #
    cB
    cbr
    cfv
    #
    chft
    co
    #
    @2
    @3
    chil
    wcel
    @4
    @7
    wceq
    cA
    cB
    hvmulcl
    vx
    @3
    brafval
    syl
    @2
    @10
    vx
    chil
    @8
    @5
    @9
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    @7
    @0
    @8
    cc
    wcel
    chil
    cc
    @9
    wf
    @10
    @13
    wceq
    @1
    cA
    cjcl
    cB
    brafn
    vx
    @8
    @9
    hfmmval
    syl2an
    @2
    vx
    chil
    @6
    @12
    @2
    @5
    chil
    wcel
    #
    wa
    #
    @6
    @8
    @5
    cB
    csp
    co
    #
    cmul
    co
    #
    @12
    @0
    @14
    @1
    @6
    @17
    wceq
    #
    @0
    @14
    @1
    @18
    cA
    @5
    cB
    his5
    3expa
    an32s
    @15
    @11
    @16
    @8
    cmul
    @1
    @14
    @11
    @16
    wceq
    @0
    cB
    @5
    braval
    adantll
    oveq2d
    eqtr4d
    mpteq2dva
    eqtr4d
    eqtr4d
end
