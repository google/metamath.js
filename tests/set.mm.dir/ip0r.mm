include "cphl.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cstv.mm"
include "cfv.mm"
include "ip0l.mm"
include "fveq2d.mm"
include "wceq.mm"
include "clmod.mm"
include "phllmod.mm"
include "adantr.mm"
include "lmod0vcl.mm"
include "syl.mm"
include "eqid.mm"
include "ipcj.mm"
include "3expa.mm"
include "an32s.mm"
include "mpdan.mm"
include "csr.mm"
include "phlsrng.mm"
include "srng0.mm"
include "3eqtr3d.mm"

theorem ip0r
  let cA: class A
  let cF: class F
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cG: class G
  let c.as: class .*
  let cK: class K
  let c.x: class .x.
  assume phlsrng.f: |- F = ( Scalar ` W )
  assume phllmhm.h: |- ., = ( .i ` W )
  assume phllmhm.v: |- V = ( Base ` W )
  assume ip0l.z: |- Z = ( 0g ` F )
  assume ip0l.o: |- .0. = ( 0g ` W )


  assert |- ( ( W e. PreHil /\ A e. V ) -> ( A ., .0. ) = Z )

  proof
    cW
    cphl
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    c.0
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
    cZ
    @4
    cfv
    #
    cA
    c.0
    c.xi
    co
    #
    cZ
    @2
    @3
    cZ
    @4
    cA
    cF
    c.xi
    cV
    cW
    c.0
    cZ
    phlsrng.f
    phllmhm.h
    phllmhm.v
    ip0l.z
    ip0l.o
    ip0l
    fveq2d
    @2
    c.0
    cV
    wcel
    #
    @5
    @7
    wceq
    #
    @2
    cW
    clmod
    wcel
    #
    @8
    @0
    @10
    @1
    cW
    phllmod
    adantr
    cV
    cW
    c.0
    phllmhm.v
    ip0l.o
    lmod0vcl
    syl
    @0
    @8
    @1
    @9
    @0
    @8
    @1
    @9
    c.0
    cA
    cF
    c.xi
    @4
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @4
    eqid
    #
    ipcj
    3expa
    an32s
    mpdan
    @2
    cF
    csr
    wcel
    #
    @6
    cZ
    wceq
    @0
    @12
    @1
    cF
    cW
    phlsrng.f
    phlsrng
    adantr
    cF
    @4
    cZ
    @11
    ip0l.z
    srng0
    syl
    3eqtr3d
end
