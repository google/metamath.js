include "cphl.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cplusg.mm"
include "cfv.mm"
include "simpl.mm"
include "simpr1.mm"
include "cgrp.mm"
include "clmod.mm"
include "phllmod.mm"
include "adantr.mm"
include "lmodgrp.mm"
include "syl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "ipdi.mm"
include "syl13anc.mm"
include "grpnpcan.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "cbs.mm"
include "wb.mm"
include "lmodfgrp.mm"
include "ipcl.mm"
include "grpsubadd.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem ipsubdi
  let cA: class A
  let cB: class B
  let cC: class C
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


  assert |- ( ( W e. PreHil /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( A ., ( B .- C ) ) = ( ( A ., B ) S ( A ., C ) ) )

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
    cS
    co
    #
    cA
    cB
    cC
    c.mi
    co
    #
    c.xi
    co
    #
    @5
    @8
    @10
    wceq
    #
    @10
    @7
    cF
    cplusg
    cfv
    #
    co
    #
    @6
    wceq
    #
    @5
    cA
    @9
    cC
    cW
    cplusg
    cfv
    #
    co
    #
    c.xi
    co
    #
    @13
    @6
    @5
    @0
    @1
    @9
    cV
    wcel
    #
    @3
    @17
    @13
    wceq
    @0
    @4
    simpl
    #
    @0
    @1
    @2
    @3
    simpr1
    #
    @5
    cW
    cgrp
    wcel
    #
    @2
    @3
    @18
    @5
    cW
    clmod
    wcel
    #
    @21
    @0
    @22
    @4
    cW
    phllmod
    adantr
    #
    cW
    lmodgrp
    syl
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
    cV
    cW
    c.mi
    cB
    cC
    phllmhm.v
    ipsubdir.m
    grpsubcl
    syl3anc
    #
    @26
    cA
    @9
    cC
    @15
    @12
    cF
    c.xi
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @15
    eqid
    #
    @12
    eqid
    #
    ipdi
    syl13anc
    @5
    @16
    cB
    cA
    c.xi
    @5
    @21
    @2
    @3
    @16
    cB
    wceq
    @24
    @25
    @26
    cV
    @15
    cW
    c.mi
    cB
    cC
    phllmhm.v
    @28
    ipsubdir.m
    grpnpcan
    syl3anc
    oveq2d
    eqtr3d
    @5
    cF
    cgrp
    wcel
    #
    @6
    cF
    cbs
    cfv
    #
    wcel
    #
    @7
    @31
    wcel
    #
    @10
    @31
    wcel
    #
    @11
    @14
    wb
    @5
    @22
    @30
    @23
    cF
    cW
    phlsrng.f
    lmodfgrp
    syl
    @5
    @0
    @1
    @2
    @32
    @19
    @20
    @25
    cA
    cB
    cF
    c.xi
    @31
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @31
    eqid
    #
    ipcl
    syl3anc
    @5
    @0
    @1
    @3
    @33
    @19
    @20
    @26
    cA
    cC
    cF
    c.xi
    @31
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @35
    ipcl
    syl3anc
    @5
    @0
    @1
    @18
    @34
    @19
    @20
    @27
    cA
    @9
    cF
    c.xi
    @31
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @35
    ipcl
    syl3anc
    @31
    @12
    cF
    cS
    @6
    @7
    @10
    @35
    @29
    ipsubdir.s
    grpsubadd
    syl13anc
    mpbird
    eqcomd
end
