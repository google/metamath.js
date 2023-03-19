include "cphl.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "csr.mm"
include "phlsrng.mm"
include "adantr.mm"
include "simpr3.mm"
include "srngcl.mm"
include "syl2anc.mm"
include "ipassr.mm"
include "syl13anc.mm"
include "srngnvl.mm"
include "oveq2d.mm"
include "eqtr2d.mm"

theorem ipassr2
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


  assert |- ( ( W e. PreHil /\ ( A e. V /\ B e. V /\ C e. K ) ) -> ( ( A ., B ) .X. C ) = ( A ., ( ( .* ` C ) .x. B ) ) )

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
    c.as
    cfv
    #
    cB
    c.x
    co
    c.xi
    co
    #
    cA
    cB
    c.xi
    co
    #
    @6
    c.as
    cfv
    #
    c.xp
    co
    #
    @8
    cC
    c.xp
    co
    @5
    @0
    @1
    @2
    @6
    cK
    wcel
    #
    @7
    @10
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    @5
    cF
    csr
    wcel
    #
    @3
    @11
    @0
    @12
    @4
    cF
    cW
    phlsrng.f
    phlsrng
    adantr
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    cK
    cF
    c.as
    cC
    ipassr.i
    ipdir.f
    srngcl
    syl2anc
    cA
    cB
    @6
    c.x
    c.xp
    cF
    c.xi
    c.as
    cK
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    ipdir.f
    ipass.s
    ipass.p
    ipassr.i
    ipassr
    syl13anc
    @5
    @9
    cC
    @8
    c.xp
    @5
    @12
    @3
    @9
    cC
    wceq
    @13
    @14
    cK
    cF
    c.as
    cC
    ipassr.i
    ipdir.f
    srngnvl
    syl2anc
    oveq2d
    eqtr2d
end
