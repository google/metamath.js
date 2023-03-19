include "cphl.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "crglmod.mm"
include "cghm.mm"
include "wceq.mm"
include "clmhm.mm"
include "eqid.mm"
include "phllmhm.mm"
include "3ad2antr3.mm"
include "lmghm.mm"
include "syl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "cplusg.mm"
include "rlmplusg.mm"
include "eqtri.mm"
include "ghmlin.mm"
include "syl3anc.mm"
include "clmod.mm"
include "phllmod.mm"
include "lmodvacl.mm"
include "syl3an1.mm"
include "3adant3r3.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"

theorem ipdir
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.pd: class .+^
  let cF: class F
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let c.as: class .*
  let cK: class K
  let c.0: class .0.
  let c.x: class .x.
  let cZ: class Z
  assume phlsrng.f: |- F = ( Scalar ` W )
  assume phllmhm.h: |- ., = ( .i ` W )
  assume phllmhm.v: |- V = ( Base ` W )
  assume ipdir.g: |- .+ = ( +g ` W )
  assume ipdir.p: |- .+^ = ( +g ` F )


  assert |- ( ( W e. PreHil /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( ( A .+ B ) ., C ) = ( ( A ., C ) .+^ ( B ., C ) ) )

  proof
    cW
    cphl
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    wa
    #
    cA
    cB
    c.pl
    co
    #
    vx
    cV
    vx
    cv
    #
    cC
    c.xi
    co
    #
    cmpt
    #
    cfv
    #
    cA
    @8
    cfv
    #
    cB
    @8
    cfv
    #
    c.pd
    co
    #
    @5
    cC
    c.xi
    co
    #
    cA
    cC
    c.xi
    co
    #
    cB
    cC
    c.xi
    co
    #
    c.pd
    co
    @4
    @8
    cW
    cF
    crglmod
    cfv
    #
    cghm
    co
    wcel
    #
    @1
    @2
    @9
    @12
    wceq
    @4
    @8
    cW
    @16
    clmhm
    co
    wcel
    #
    @17
    @0
    @1
    @3
    @18
    @2
    vx
    cC
    cF
    @8
    c.xi
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @8
    eqid
    #
    phllmhm
    3ad2antr3
    cW
    @16
    @8
    lmghm
    syl
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    c.pl
    c.pd
    cW
    @16
    cA
    @8
    cB
    cV
    phllmhm.v
    ipdir.g
    c.pd
    cF
    cplusg
    cfv
    @16
    cplusg
    cfv
    ipdir.p
    cF
    rlmplusg
    eqtri
    ghmlin
    syl3anc
    @4
    @5
    cV
    wcel
    #
    @9
    @13
    wceq
    @0
    @1
    @2
    @22
    @3
    @0
    cW
    clmod
    wcel
    @1
    @2
    @22
    cW
    phllmod
    c.pl
    cV
    cW
    cA
    cB
    phllmhm.v
    ipdir.g
    lmodvacl
    syl3an1
    3adant3r3
    vx
    @5
    @7
    @13
    cV
    @8
    @6
    @5
    cC
    c.xi
    oveq1
    @19
    @6
    cC
    c.xi
    ovex
    #
    fvmpt3i
    syl
    @4
    @10
    @14
    @11
    @15
    c.pd
    @4
    @1
    @10
    @14
    wceq
    @20
    vx
    cA
    @7
    @14
    cV
    @8
    @6
    cA
    cC
    c.xi
    oveq1
    @19
    @23
    fvmpt3i
    syl
    @4
    @2
    @11
    @15
    wceq
    @21
    vx
    cB
    @7
    @15
    cV
    @8
    @6
    cB
    cC
    c.xi
    oveq1
    @19
    @23
    fvmpt3i
    syl
    oveq12d
    3eqtr3d
end
