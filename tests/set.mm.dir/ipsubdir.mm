include "cphl.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cplusg.mm"
include "cfv.mm"
include "simpl.mm"
include "cgrp.mm"
include "clmod.mm"
include "phllmod.mm"
include "adantr.mm"
include "lmodgrp.mm"
include "syl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "eqid.mm"
include "ipdir.mm"
include "syl13anc.mm"
include "grpnpcan.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "cbs.mm"
include "wb.mm"
include "lmodfgrp.mm"
include "ipcl.mm"
include "grpsubadd.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem ipsubdir
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


  assert |- ( ( W e. PreHil /\ ( A e. V /\ B e. V /\ C e. V ) ) -> ( ( A .- B ) ., C ) = ( ( A ., C ) S ( B ., C ) ) )

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
    cC
    c.xi
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
    cA
    cB
    c.mi
    co
    #
    cC
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
    @9
    cB
    cW
    cplusg
    cfv
    #
    co
    #
    cC
    c.xi
    co
    #
    @13
    @6
    @5
    @0
    @9
    cV
    wcel
    #
    @2
    @3
    @17
    @13
    wceq
    @0
    @4
    simpl
    #
    @5
    cW
    cgrp
    wcel
    #
    @1
    @2
    @18
    @5
    cW
    clmod
    wcel
    #
    @20
    @0
    @21
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
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    cV
    cW
    c.mi
    cA
    cB
    phllmhm.v
    ipsubdir.m
    grpsubcl
    syl3anc
    #
    @25
    @0
    @1
    @2
    @3
    simpr3
    #
    @9
    cB
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
    ipdir
    syl13anc
    @5
    @16
    cA
    cC
    c.xi
    @5
    @20
    @1
    @2
    @16
    cA
    wceq
    @23
    @24
    @25
    cV
    @15
    cW
    c.mi
    cA
    cB
    phllmhm.v
    @28
    ipsubdir.m
    grpnpcan
    syl3anc
    oveq1d
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
    @21
    @30
    @22
    cF
    cW
    phlsrng.f
    lmodfgrp
    syl
    @5
    @0
    @1
    @3
    @32
    @19
    @24
    @27
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
    @31
    eqid
    #
    ipcl
    syl3anc
    @5
    @0
    @2
    @3
    @33
    @19
    @25
    @27
    cB
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
    @18
    @3
    @34
    @19
    @26
    @27
    @9
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
