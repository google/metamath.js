include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "cplusg.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "cmulr.mm"
include "simpl.mm"
include "lmod1cl.mm"
include "adantr.mm"
include "simpr3.mm"
include "simpr2.mm"
include "eqid.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "eqcomd.mm"
include "crg.mm"
include "lmodring.mm"
include "simp3.mm"
include "ringlidm.mm"
include "syl2an.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "grpinvcl.mm"
include "lmodvsdir.mm"
include "grprinv.mm"
include "lmod0vs.mm"
include "3ad2antr2.mm"
include "eqtrd.mm"
include "3eqtr2d.mm"
include "sylan9eqr.mm"
include "ex.mm"

theorem ldepsprlem
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vf: setvar f
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume snlindsntor.b: |- B = ( Base ` M )
  assume snlindsntor.r: |- R = ( Scalar ` M )
  assume snlindsntor.s: |- S = ( Base ` R )
  assume snlindsntor.0: |- .0. = ( 0g ` R )
  assume snlindsntor.z: |- Z = ( 0g ` M )
  assume snlindsntor.t: |- .x. = ( .s ` M )
  assume ldepsprlem.1: |- .1. = ( 1r ` R )
  assume ldepsprlem.n: |- N = ( invg ` R )


  assert |- ( ( M e. LMod /\ ( X e. B /\ Y e. B /\ A e. S ) ) -> ( X = ( A .x. Y ) -> ( ( .1. .x. X ) ( +g ` M ) ( ( N ` A ) .x. Y ) ) = Z ) )

  proof
    cM
    clmod
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cA
    cS
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cA
    cY
    c.x
    co
    #
    wceq
    #
    c.1
    cX
    c.x
    co
    #
    cA
    cN
    cfv
    #
    cY
    c.x
    co
    #
    cM
    cplusg
    cfv
    #
    co
    #
    cZ
    wceq
    @7
    @5
    @12
    c.1
    @6
    c.x
    co
    #
    @10
    @11
    co
    #
    cZ
    @7
    @8
    @13
    @10
    @11
    cX
    @6
    c.1
    c.x
    oveq2
    oveq1d
    @5
    @14
    c.1
    cA
    cR
    cmulr
    cfv
    #
    co
    #
    cY
    c.x
    co
    #
    @10
    @11
    co
    #
    cZ
    @5
    @13
    @17
    @10
    @11
    @5
    @17
    @13
    @5
    @0
    c.1
    cS
    wcel
    #
    @3
    @2
    @17
    @13
    wceq
    @0
    @4
    simpl
    #
    @0
    @19
    @4
    c.1
    cR
    cS
    cM
    snlindsntor.r
    snlindsntor.s
    ldepsprlem.1
    lmod1cl
    adantr
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
    c.1
    cA
    c.x
    @15
    cR
    cS
    cB
    cM
    cY
    snlindsntor.b
    snlindsntor.r
    snlindsntor.t
    snlindsntor.s
    @15
    eqid
    #
    lmodvsass
    syl13anc
    eqcomd
    oveq1d
    @5
    @18
    @6
    @10
    @11
    co
    #
    cA
    @9
    cR
    cplusg
    cfv
    #
    co
    #
    cY
    c.x
    co
    #
    cZ
    @5
    @17
    @6
    @10
    @11
    @5
    @16
    cA
    cY
    c.x
    @0
    cR
    crg
    wcel
    @3
    @16
    cA
    wceq
    @4
    cR
    cM
    snlindsntor.r
    lmodring
    @1
    @2
    @3
    simp3
    #
    cS
    cR
    @15
    c.1
    cA
    snlindsntor.s
    @23
    ldepsprlem.1
    ringlidm
    syl2an
    oveq1d
    oveq1d
    @5
    @0
    @3
    @9
    cS
    wcel
    #
    @2
    @27
    @24
    wceq
    @20
    @21
    @0
    cR
    cgrp
    wcel
    #
    @3
    @29
    @4
    cR
    cM
    snlindsntor.r
    lmodfgrp
    #
    @28
    cS
    cR
    cN
    cA
    snlindsntor.s
    ldepsprlem.n
    grpinvcl
    syl2an
    @22
    @11
    @25
    cA
    @9
    c.x
    cR
    cS
    cB
    cM
    cY
    snlindsntor.b
    @11
    eqid
    snlindsntor.r
    snlindsntor.t
    snlindsntor.s
    @25
    eqid
    #
    lmodvsdir
    syl13anc
    @5
    @27
    c.0
    cY
    c.x
    co
    #
    cZ
    @5
    @26
    c.0
    cY
    c.x
    @0
    @30
    @3
    @26
    c.0
    wceq
    @4
    @31
    @28
    cS
    @25
    cR
    cN
    cA
    c.0
    snlindsntor.s
    @32
    snlindsntor.0
    ldepsprlem.n
    grprinv
    syl2an
    oveq1d
    @0
    @1
    @2
    @33
    cZ
    wceq
    @3
    c.x
    cR
    c.0
    cB
    cM
    cY
    cZ
    snlindsntor.b
    snlindsntor.r
    snlindsntor.t
    snlindsntor.0
    snlindsntor.z
    lmod0vs
    3ad2antr2
    eqtrd
    3eqtr2d
    eqtrd
    sylan9eqr
    ex
end
