include "cphl.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "crglmod.mm"
include "clmhm.mm"
include "wceq.mm"
include "eqid.mm"
include "phllmhm.mm"
include "3ad2antr3.mm"
include "simpr1.mm"
include "simpr2.mm"
include "cmulr.mm"
include "cvsca.mm"
include "rlmvsca.mm"
include "eqtri.mm"
include "lmhmlin.mm"
include "syl3anc.mm"
include "clmod.mm"
include "phllmod.mm"
include "adantr.mm"
include "lmodvscl.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "syl.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"

theorem ipass
  let cA: class A
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let c.xi: class .,
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let c.as: class .*
  let c.0: class .0.
  let cZ: class Z
  assume phlsrng.f: |- F = ( Scalar ` W )
  assume phllmhm.h: |- ., = ( .i ` W )
  assume phllmhm.v: |- V = ( Base ` W )
  assume ipdir.f: |- K = ( Base ` F )
  assume ipass.s: |- .x. = ( .s ` W )
  assume ipass.p: |- .X. = ( .r ` F )


  assert |- ( ( W e. PreHil /\ ( A e. K /\ B e. V /\ C e. V ) ) -> ( ( A .x. B ) ., C ) = ( A .X. ( B ., C ) ) )

  proof
    cW
    cphl
    wcel
    #
    cA
    cK
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
    #
    wa
    #
    cA
    cB
    c.x
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
    cB
    @9
    cfv
    #
    c.xp
    co
    #
    @6
    cC
    c.xi
    co
    #
    cA
    cB
    cC
    c.xi
    co
    #
    c.xp
    co
    @5
    @9
    cW
    cF
    crglmod
    cfv
    #
    clmhm
    co
    wcel
    #
    @1
    @2
    @10
    @12
    wceq
    @0
    @1
    @3
    @16
    @2
    vx
    cC
    cF
    @9
    c.xi
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @9
    eqid
    #
    phllmhm
    3ad2antr3
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
    cK
    cW
    @15
    c.x
    c.xp
    cV
    @9
    cF
    cA
    cB
    phlsrng.f
    ipdir.f
    phllmhm.v
    ipass.s
    c.xp
    cF
    cmulr
    cfv
    @15
    cvsca
    cfv
    ipass.p
    cF
    rlmvsca
    eqtri
    lmhmlin
    syl3anc
    @5
    @6
    cV
    wcel
    #
    @10
    @13
    wceq
    @5
    cW
    clmod
    wcel
    #
    @1
    @2
    @20
    @0
    @21
    @4
    cW
    phllmod
    adantr
    @18
    @19
    cA
    c.x
    cF
    cK
    cV
    cW
    cB
    phllmhm.v
    phlsrng.f
    ipass.s
    ipdir.f
    lmodvscl
    syl3anc
    vx
    @6
    @8
    @13
    cV
    @9
    @7
    @6
    cC
    c.xi
    oveq1
    @17
    @7
    cC
    c.xi
    ovex
    #
    fvmpt3i
    syl
    @5
    @11
    @14
    cA
    c.xp
    @5
    @2
    @11
    @14
    wceq
    @19
    vx
    cB
    @8
    @14
    cV
    @9
    @7
    cB
    cC
    c.xi
    oveq1
    @17
    @22
    fvmpt3i
    syl
    oveq2d
    3eqtr3d
end
