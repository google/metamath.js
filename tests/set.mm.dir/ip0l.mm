include "cphl.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cfv.mm"
include "wceq.mm"
include "clmod.mm"
include "cgrp.mm"
include "phllmod.mm"
include "lmodgrp.mm"
include "grpidcl.mm"
include "3syl.mm"
include "adantr.mm"
include "oveq1.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "crglmod.mm"
include "clmhm.mm"
include "cghm.mm"
include "phllmhm.mm"
include "lmghm.mm"
include "c0g.mm"
include "rlm0.mm"
include "eqtri.mm"
include "ghmid.mm"
include "eqtr3d.mm"

theorem ip0l
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


  assert |- ( ( W e. PreHil /\ A e. V ) -> ( .0. ., A ) = Z )

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
    vx
    cV
    vx
    cv
    #
    cA
    c.xi
    co
    #
    cmpt
    #
    cfv
    #
    c.0
    cA
    c.xi
    co
    #
    cZ
    @2
    c.0
    cV
    wcel
    #
    @6
    @7
    wceq
    @0
    @8
    @1
    @0
    cW
    clmod
    wcel
    cW
    cgrp
    wcel
    @8
    cW
    phllmod
    cW
    lmodgrp
    cV
    cW
    c.0
    phllmhm.v
    ip0l.o
    grpidcl
    3syl
    adantr
    vx
    c.0
    @4
    @7
    cV
    @5
    @3
    c.0
    cA
    c.xi
    oveq1
    @5
    eqid
    #
    c.0
    cA
    c.xi
    ovex
    fvmpt
    syl
    @2
    @5
    cW
    cF
    crglmod
    cfv
    #
    clmhm
    co
    wcel
    @5
    cW
    @10
    cghm
    co
    wcel
    @6
    cZ
    wceq
    vx
    cA
    cF
    @5
    c.xi
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @9
    phllmhm
    cW
    @10
    @5
    lmghm
    cW
    @10
    @5
    c.0
    cZ
    ip0l.o
    cZ
    cF
    c0g
    cfv
    @10
    c0g
    cfv
    ip0l.z
    cF
    rlm0
    eqtri
    ghmid
    3syl
    eqtr3d
end
