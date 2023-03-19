include "cphl.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr3.mm"
include "simpr2.mm"
include "simpr1.mm"
include "ipass.mm"
include "syl13anc.mm"
include "fveq2d.mm"
include "clmod.mm"
include "phllmod.mm"
include "adantr.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "ipcj.mm"
include "csr.mm"
include "phlsrng.mm"
include "ipcl.mm"
include "srngmul.mm"
include "3eqtr3d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem ipassr
  let cA: class A
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let c.xi: class .,
  let c.as: class .*
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let c.0: class .0.
  let cZ: class Z
  assume phlsrng.f: |- F = ( Scalar ` W )
  assume phllmhm.h: |- ., = ( .i ` W )
  assume phllmhm.v: |- V = ( Base ` W )
  assume ipdir.f: |- K = ( Base ` F )
  assume ipass.s: |- .x. = ( .s ` W )
  assume ipass.p: |- .X. = ( .r ` F )
  assume ipassr.i: |- .* = ( *r ` F )


  assert |- ( ( W e. PreHil /\ ( A e. V /\ B e. V /\ C e. K ) ) -> ( A ., ( C .x. B ) ) = ( ( A ., B ) .X. ( .* ` C ) ) )

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
    cK
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cC
    cB
    c.x
    co
    #
    c.xi
    co
    #
    cB
    cA
    c.xi
    co
    #
    c.as
    cfv
    #
    cC
    c.as
    cfv
    #
    c.xp
    co
    #
    cA
    cB
    c.xi
    co
    #
    @10
    c.xp
    co
    @5
    @6
    cA
    c.xi
    co
    #
    c.as
    cfv
    #
    cC
    @8
    c.xp
    co
    #
    c.as
    cfv
    #
    @7
    @11
    @5
    @13
    @15
    c.as
    @5
    @0
    @3
    @2
    @1
    @13
    @15
    wceq
    @0
    @4
    simpl
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    cC
    cB
    cA
    c.x
    c.xp
    cF
    c.xi
    cK
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    ipdir.f
    ipass.s
    ipass.p
    ipass
    syl13anc
    fveq2d
    @5
    @0
    @6
    cV
    wcel
    #
    @1
    @14
    @7
    wceq
    @17
    @5
    cW
    clmod
    wcel
    #
    @3
    @2
    @21
    @0
    @22
    @4
    cW
    phllmod
    adantr
    @18
    @19
    cC
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
    @20
    @6
    cA
    cF
    c.xi
    c.as
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    ipassr.i
    ipcj
    syl3anc
    @5
    cF
    csr
    wcel
    #
    @3
    @8
    cK
    wcel
    #
    @16
    @11
    wceq
    @0
    @23
    @4
    cF
    cW
    phlsrng.f
    phlsrng
    adantr
    @18
    @5
    @0
    @2
    @1
    @24
    @17
    @19
    @20
    cB
    cA
    cF
    c.xi
    cK
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    ipdir.f
    ipcl
    syl3anc
    cK
    cF
    c.xp
    c.as
    cC
    @8
    ipassr.i
    ipdir.f
    ipass.p
    srngmul
    syl3anc
    3eqtr3d
    @5
    @9
    @12
    @10
    c.xp
    @5
    @0
    @2
    @1
    @9
    @12
    wceq
    @17
    @19
    @20
    cB
    cA
    cF
    c.xi
    c.as
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    ipassr.i
    ipcj
    syl3anc
    oveq1d
    eqtrd
end
