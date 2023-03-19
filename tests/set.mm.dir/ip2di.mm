include "co.mm"
include "cphl.mm"
include "wcel.mm"
include "wceq.mm"
include "clmod.mm"
include "phllmod.mm"
include "syl.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "ipdir.mm"
include "syl13anc.mm"
include "ipdi.mm"
include "ccmn.mm"
include "cbs.mm"
include "cfv.mm"
include "csr.mm"
include "crg.mm"
include "phlsrng.mm"
include "srngring.mm"
include "ringcmn.mm"
include "4syl.mm"
include "eqid.mm"
include "ipcl.mm"
include "cmncom.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "cmn4.mm"
include "syl122anc.mm"
include "3eqtrd.mm"

theorem ip2di
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
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
  assume ip2di.1: |- ( ph -> W e. PreHil )
  assume ip2di.2: |- ( ph -> A e. V )
  assume ip2di.3: |- ( ph -> B e. V )
  assume ip2di.4: |- ( ph -> C e. V )
  assume ip2di.5: |- ( ph -> D e. V )


  assert |- ( ph -> ( ( A .+ B ) ., ( C .+ D ) ) = ( ( ( A ., C ) .+^ ( B ., D ) ) .+^ ( ( A ., D ) .+^ ( B ., C ) ) ) )

  proof
    wph
    cA
    cB
    c.pl
    co
    cC
    cD
    c.pl
    co
    #
    c.xi
    co
    #
    cA
    @0
    c.xi
    co
    #
    cB
    @0
    c.xi
    co
    #
    c.pd
    co
    #
    cA
    cC
    c.xi
    co
    #
    cA
    cD
    c.xi
    co
    #
    c.pd
    co
    #
    cB
    cD
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
    #
    c.pd
    co
    #
    @5
    @8
    c.pd
    co
    @6
    @9
    c.pd
    co
    c.pd
    co
    #
    wph
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
    @0
    cV
    wcel
    #
    @1
    @4
    wceq
    ip2di.1
    ip2di.2
    ip2di.3
    wph
    cW
    clmod
    wcel
    #
    cC
    cV
    wcel
    #
    cD
    cV
    wcel
    #
    @16
    wph
    @13
    @17
    ip2di.1
    cW
    phllmod
    syl
    ip2di.4
    ip2di.5
    c.pl
    cV
    cW
    cC
    cD
    phllmhm.v
    ipdir.g
    lmodvacl
    syl3anc
    cA
    cB
    @0
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
    wph
    @2
    @7
    @3
    @10
    c.pd
    wph
    @13
    @14
    @18
    @19
    @2
    @7
    wceq
    ip2di.1
    ip2di.2
    ip2di.4
    ip2di.5
    cA
    cC
    cD
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
    ipdi
    syl13anc
    wph
    @3
    @9
    @8
    c.pd
    co
    #
    @10
    wph
    @13
    @15
    @18
    @19
    @3
    @20
    wceq
    ip2di.1
    ip2di.3
    ip2di.4
    ip2di.5
    cB
    cC
    cD
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
    ipdi
    syl13anc
    wph
    cF
    ccmn
    wcel
    #
    @9
    cF
    cbs
    cfv
    #
    wcel
    #
    @8
    @22
    wcel
    #
    @20
    @10
    wceq
    wph
    @13
    cF
    csr
    wcel
    cF
    crg
    wcel
    @21
    ip2di.1
    cF
    cW
    phlsrng.f
    phlsrng
    cF
    srngring
    cF
    ringcmn
    4syl
    #
    wph
    @13
    @15
    @18
    @23
    ip2di.1
    ip2di.3
    ip2di.4
    cB
    cC
    cF
    c.xi
    @22
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @22
    eqid
    #
    ipcl
    syl3anc
    #
    wph
    @13
    @15
    @19
    @24
    ip2di.1
    ip2di.3
    ip2di.5
    cB
    cD
    cF
    c.xi
    @22
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @26
    ipcl
    syl3anc
    #
    @22
    c.pd
    cF
    @9
    @8
    @26
    ipdir.p
    cmncom
    syl3anc
    eqtrd
    oveq12d
    wph
    @21
    @5
    @22
    wcel
    #
    @6
    @22
    wcel
    #
    @24
    @23
    @11
    @12
    wceq
    @25
    wph
    @13
    @14
    @18
    @29
    ip2di.1
    ip2di.2
    ip2di.4
    cA
    cC
    cF
    c.xi
    @22
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @26
    ipcl
    syl3anc
    wph
    @13
    @14
    @19
    @30
    ip2di.1
    ip2di.2
    ip2di.5
    cA
    cD
    cF
    c.xi
    @22
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @26
    ipcl
    syl3anc
    @28
    @27
    @22
    c.pd
    cF
    @9
    @5
    @6
    @8
    @26
    ipdir.p
    cmn4
    syl122anc
    3eqtrd
end
