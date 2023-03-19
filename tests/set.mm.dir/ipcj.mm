include "cphl.mm"
include "wcel.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cmpt.mm"
include "crglmod.mm"
include "clmhm.mm"
include "c0g.mm"
include "wi.mm"
include "w3a.mm"
include "clvec.mm"
include "csr.mm"
include "eqid.mm"
include "isphl.mm"
include "simp3bi.mm"
include "simp3.mm"
include "ralimi.mm"
include "syl.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem ipcj
  let cA: class A
  let cB: class B
  let cF: class F
  let c.xi: class .,
  let c.as: class .*
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cG: class G
  let cK: class K
  let c.0: class .0.
  let c.x: class .x.
  let cZ: class Z
  assume phlsrng.f: |- F = ( Scalar ` W )
  assume phllmhm.h: |- ., = ( .i ` W )
  assume phllmhm.v: |- V = ( Base ` W )
  assume ipcj.i: |- .* = ( *r ` F )


  assert |- ( ( W e. PreHil /\ A e. V /\ B e. V ) -> ( .* ` ( A ., B ) ) = ( B ., A ) )

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
    cA
    cB
    c.xi
    co
    #
    c.as
    cfv
    #
    cB
    cA
    c.xi
    co
    #
    wceq
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.xi
    co
    #
    c.as
    cfv
    #
    @8
    @7
    c.xi
    co
    #
    wceq
    #
    vy
    cV
    wral
    #
    vx
    cV
    wral
    #
    @1
    @2
    wa
    @6
    @0
    vy
    cV
    @11
    cmpt
    cW
    cF
    crglmod
    cfv
    clmhm
    co
    wcel
    #
    @7
    @7
    c.xi
    co
    cF
    c0g
    cfv
    #
    wceq
    @7
    cW
    c0g
    cfv
    #
    wceq
    wi
    #
    @13
    w3a
    #
    vx
    cV
    wral
    #
    @14
    @0
    cW
    clvec
    wcel
    cF
    csr
    wcel
    @20
    vx
    vy
    cF
    c.xi
    c.as
    cV
    cW
    @17
    @16
    phllmhm.v
    phlsrng.f
    phllmhm.h
    @17
    eqid
    ipcj.i
    @16
    eqid
    isphl
    simp3bi
    @19
    @13
    vx
    cV
    @15
    @18
    @13
    simp3
    ralimi
    syl
    @12
    @6
    cA
    @8
    c.xi
    co
    #
    c.as
    cfv
    #
    @8
    cA
    c.xi
    co
    #
    wceq
    vx
    vy
    cA
    cB
    cV
    cV
    @7
    cA
    wceq
    #
    @10
    @22
    @11
    @23
    @24
    @9
    @21
    c.as
    @7
    cA
    @8
    c.xi
    oveq1
    fveq2d
    @7
    cA
    @8
    c.xi
    oveq2
    eqeq12d
    @8
    cB
    wceq
    #
    @22
    @4
    @23
    @5
    @25
    @21
    @3
    c.as
    @8
    cB
    cA
    c.xi
    oveq2
    fveq2d
    @8
    cB
    cA
    c.xi
    oveq1
    eqeq12d
    rspc2v
    syl5com
    3impib
end
