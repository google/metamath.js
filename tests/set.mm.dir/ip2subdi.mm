include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "crg.mm"
include "wcel.mm"
include "cabl.mm"
include "clmod.mm"
include "cphl.mm"
include "phllmod.mm"
include "syl.mm"
include "lmodring.mm"
include "ringabl.mm"
include "ipcl.mm"
include "syl3anc.mm"
include "ablsubsub4.mm"
include "oveq1d.mm"
include "wceq.mm"
include "lmodvsubcl.mm"
include "ipsubdir.mm"
include "syl13anc.mm"
include "ipsubdi.mm"
include "oveq12d.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpsubcl.mm"
include "ablsubsub.mm"
include "3eqtrd.mm"
include "ringacl.mm"
include "abladdsub.mm"
include "3eqtr4d.mm"

theorem ip2subdi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let c.xi: class .,
  let c.mi: class .-
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
  assume ipsubdir.m: |- .- = ( -g ` W )
  assume ipsubdir.s: |- S = ( -g ` F )
  assume ip2subdi.p: |- .+ = ( +g ` F )
  assume ip2subdi.1: |- ( ph -> W e. PreHil )
  assume ip2subdi.2: |- ( ph -> A e. V )
  assume ip2subdi.3: |- ( ph -> B e. V )
  assume ip2subdi.4: |- ( ph -> C e. V )
  assume ip2subdi.5: |- ( ph -> D e. V )


  assert |- ( ph -> ( ( A .- B ) ., ( C .- D ) ) = ( ( ( A ., C ) .+ ( B ., D ) ) S ( ( A ., D ) .+ ( B ., C ) ) ) )

  proof
    wph
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
    cS
    co
    #
    cB
    cC
    c.xi
    co
    #
    cS
    co
    #
    cB
    cD
    c.xi
    co
    #
    c.pl
    co
    #
    @0
    @1
    @3
    c.pl
    co
    #
    cS
    co
    #
    @5
    c.pl
    co
    #
    cA
    cB
    c.mi
    co
    cC
    cD
    c.mi
    co
    #
    c.xi
    co
    #
    @0
    @5
    c.pl
    co
    @7
    cS
    co
    #
    wph
    @4
    @8
    @5
    c.pl
    wph
    cF
    cbs
    cfv
    #
    c.pl
    cF
    cS
    @0
    @1
    @3
    @13
    eqid
    #
    ip2subdi.p
    ipsubdir.s
    wph
    cF
    crg
    wcel
    #
    cF
    cabl
    wcel
    #
    wph
    cW
    clmod
    wcel
    #
    @15
    wph
    cW
    cphl
    wcel
    #
    @17
    ip2subdi.1
    cW
    phllmod
    syl
    #
    cF
    cW
    phlsrng.f
    lmodring
    syl
    #
    cF
    ringabl
    syl
    #
    wph
    @18
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    @0
    @13
    wcel
    #
    ip2subdi.1
    ip2subdi.2
    ip2subdi.4
    cA
    cC
    cF
    c.xi
    @13
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @14
    ipcl
    syl3anc
    #
    wph
    @18
    @22
    cD
    cV
    wcel
    #
    @1
    @13
    wcel
    #
    ip2subdi.1
    ip2subdi.2
    ip2subdi.5
    cA
    cD
    cF
    c.xi
    @13
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @14
    ipcl
    syl3anc
    #
    wph
    @18
    cB
    cV
    wcel
    #
    @23
    @3
    @13
    wcel
    #
    ip2subdi.1
    ip2subdi.3
    ip2subdi.4
    cB
    cC
    cF
    c.xi
    @13
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @14
    ipcl
    syl3anc
    #
    ablsubsub4
    oveq1d
    wph
    @11
    cA
    @10
    c.xi
    co
    #
    cB
    @10
    c.xi
    co
    #
    cS
    co
    #
    @2
    @3
    @5
    cS
    co
    #
    cS
    co
    @6
    wph
    @18
    @22
    @29
    @10
    cV
    wcel
    #
    @11
    @34
    wceq
    ip2subdi.1
    ip2subdi.2
    ip2subdi.3
    wph
    @17
    @23
    @26
    @36
    @19
    ip2subdi.4
    ip2subdi.5
    c.mi
    cV
    cW
    cC
    cD
    phllmhm.v
    ipsubdir.m
    lmodvsubcl
    syl3anc
    cA
    cB
    @10
    cS
    cF
    c.xi
    c.mi
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    ipsubdir.m
    ipsubdir.s
    ipsubdir
    syl13anc
    wph
    @32
    @2
    @33
    @35
    cS
    wph
    @18
    @22
    @23
    @26
    @32
    @2
    wceq
    ip2subdi.1
    ip2subdi.2
    ip2subdi.4
    ip2subdi.5
    cA
    cC
    cD
    cS
    cF
    c.xi
    c.mi
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    ipsubdir.m
    ipsubdir.s
    ipsubdi
    syl13anc
    wph
    @18
    @29
    @23
    @26
    @33
    @35
    wceq
    ip2subdi.1
    ip2subdi.3
    ip2subdi.4
    ip2subdi.5
    cB
    cC
    cD
    cS
    cF
    c.xi
    c.mi
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    ipsubdir.m
    ipsubdir.s
    ipsubdi
    syl13anc
    oveq12d
    wph
    @13
    c.pl
    cF
    cS
    @2
    @3
    @5
    @14
    ip2subdi.p
    ipsubdir.s
    @21
    wph
    cF
    cgrp
    wcel
    #
    @24
    @27
    @2
    @13
    wcel
    wph
    @15
    @37
    @20
    cF
    ringgrp
    syl
    @25
    @28
    @13
    cF
    cS
    @0
    @1
    @14
    ipsubdir.s
    grpsubcl
    syl3anc
    @31
    wph
    @18
    @29
    @26
    @5
    @13
    wcel
    #
    ip2subdi.1
    ip2subdi.3
    ip2subdi.5
    cB
    cD
    cF
    c.xi
    @13
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @14
    ipcl
    syl3anc
    #
    ablsubsub
    3eqtrd
    wph
    @16
    @24
    @38
    @7
    @13
    wcel
    #
    @12
    @9
    wceq
    @21
    @25
    @39
    wph
    @15
    @27
    @30
    @40
    @20
    @28
    @31
    @13
    c.pl
    cF
    @1
    @3
    @14
    ip2subdi.p
    ringacl
    syl3anc
    @13
    c.pl
    cF
    cS
    @0
    @5
    @7
    @14
    ip2subdi.p
    ipsubdir.s
    abladdsub
    syl13anc
    3eqtr4d
end
