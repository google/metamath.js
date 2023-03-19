include "cphl.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cstv.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "simpr1.mm"
include "ipdir.mm"
include "syl13anc.mm"
include "fveq2d.mm"
include "csr.mm"
include "cbs.mm"
include "phlsrng.mm"
include "adantr.mm"
include "eqid.mm"
include "ipcl.mm"
include "syl3anc.mm"
include "srngadd.mm"
include "eqtrd.mm"
include "clmod.mm"
include "phllmod.mm"
include "lmodvacl.mm"
include "ipcj.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"

theorem ipdi
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


  assert |- ( ( W e. PreHil /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( A ., ( B .+ C ) ) = ( ( A ., B ) .+^ ( A ., C ) ) )

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
    #
    wa
    #
    cB
    cC
    c.pl
    co
    #
    cA
    c.xi
    co
    #
    cF
    cstv
    cfv
    #
    cfv
    #
    cB
    cA
    c.xi
    co
    #
    @8
    cfv
    #
    cC
    cA
    c.xi
    co
    #
    @8
    cfv
    #
    c.pd
    co
    #
    cA
    @6
    c.xi
    co
    #
    cA
    cB
    c.xi
    co
    #
    cA
    cC
    c.xi
    co
    #
    c.pd
    co
    @5
    @9
    @10
    @12
    c.pd
    co
    #
    @8
    cfv
    #
    @14
    @5
    @7
    @18
    @8
    @5
    @0
    @2
    @3
    @1
    @7
    @18
    wceq
    @0
    @4
    simpl
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
    simpr3
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    cB
    cC
    cA
    c.pl
    c.pd
    cF
    c.xi
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    ipdir.g
    ipdir.p
    ipdir
    syl13anc
    fveq2d
    @5
    cF
    csr
    wcel
    #
    @10
    cF
    cbs
    cfv
    #
    wcel
    #
    @12
    @25
    wcel
    #
    @19
    @14
    wceq
    @0
    @24
    @4
    cF
    cW
    phlsrng.f
    phlsrng
    adantr
    @5
    @0
    @2
    @1
    @26
    @20
    @21
    @23
    cB
    cA
    cF
    c.xi
    @25
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @25
    eqid
    #
    ipcl
    syl3anc
    @5
    @0
    @3
    @1
    @27
    @20
    @22
    @23
    cC
    cA
    cF
    c.xi
    @25
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @28
    ipcl
    syl3anc
    @25
    c.pd
    cF
    @8
    @10
    @12
    @8
    eqid
    #
    @28
    ipdir.p
    srngadd
    syl3anc
    eqtrd
    @5
    @0
    @6
    cV
    wcel
    #
    @1
    @9
    @15
    wceq
    @20
    @5
    cW
    clmod
    wcel
    #
    @2
    @3
    @30
    @0
    @31
    @4
    cW
    phllmod
    adantr
    @21
    @22
    c.pl
    cV
    cW
    cB
    cC
    phllmhm.v
    ipdir.g
    lmodvacl
    syl3anc
    @23
    @6
    cA
    cF
    c.xi
    @8
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @29
    ipcj
    syl3anc
    @5
    @11
    @16
    @13
    @17
    c.pd
    @5
    @0
    @2
    @1
    @11
    @16
    wceq
    @20
    @21
    @23
    cB
    cA
    cF
    c.xi
    @8
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @29
    ipcj
    syl3anc
    @5
    @0
    @3
    @1
    @13
    @17
    wceq
    @20
    @22
    @23
    cC
    cA
    cF
    c.xi
    @8
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @29
    ipcj
    syl3anc
    oveq12d
    3eqtr3d
end
