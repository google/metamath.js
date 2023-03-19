include "caddc.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "coe1tmmul2.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "nn0addcld.mm"
include "breq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "ifbieq1d.mm"
include "eqid.mm"
include "ovex.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"
include "cr.mm"
include "nn0red.mm"
include "nn0addge1.mm"
include "syl2anc.mm"
include "iftrued.mm"
include "nn0cnd.mm"
include "pncan2d.mm"
include "3eqtrd.mm"
include "eqtrd.mm"

theorem coe1tmmul2fv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let c.xp: class .X.
  let c.ex: class .^
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  assume coe1tm.z: |- .0. = ( 0g ` R )
  assume coe1tm.k: |- K = ( Base ` R )
  assume coe1tm.p: |- P = ( Poly1 ` R )
  assume coe1tm.x: |- X = ( var1 ` R )
  assume coe1tm.m: |- .x. = ( .s ` P )
  assume coe1tm.n: |- N = ( mulGrp ` P )
  assume coe1tm.e: |- .^ = ( .g ` N )
  assume coe1tmmul.b: |- B = ( Base ` P )
  assume coe1tmmul.t: |- .xb = ( .r ` P )
  assume coe1tmmul.u: |- .X. = ( .r ` R )
  assume coe1tmmul.a: |- ( ph -> A e. B )
  assume coe1tmmul.r: |- ( ph -> R e. Ring )
  assume coe1tmmul.c: |- ( ph -> C e. K )
  assume coe1tmmul.d: |- ( ph -> D e. NN0 )
  assume coe1tmmul2fv.y: |- ( ph -> Y e. NN0 )


  assert |- ( ph -> ( ( coe1 ` ( A .xb ( C .x. ( D .^ X ) ) ) ) ` ( D + Y ) ) = ( ( ( coe1 ` A ) ` Y ) .X. C ) )

  proof
    wph
    cD
    cY
    caddc
    co
    #
    cA
    cC
    cD
    cX
    c.ex
    co
    c.x
    co
    c.xb
    co
    cco1
    cfv
    #
    cfv
    @0
    vx
    cn0
    cD
    vx
    cv
    #
    cle
    wbr
    #
    @2
    cD
    cmin
    co
    #
    cA
    cco1
    cfv
    #
    cfv
    #
    cC
    c.xp
    co
    #
    c.0
    cif
    #
    cmpt
    #
    cfv
    #
    cY
    @5
    cfv
    #
    cC
    c.xp
    co
    #
    wph
    @0
    @1
    @9
    wph
    vx
    cA
    cB
    cC
    cD
    cP
    cR
    c.xb
    c.x
    c.xp
    c.ex
    cK
    cN
    cX
    c.0
    coe1tm.z
    coe1tm.k
    coe1tm.p
    coe1tm.x
    coe1tm.m
    coe1tm.n
    coe1tm.e
    coe1tmmul.b
    coe1tmmul.t
    coe1tmmul.u
    coe1tmmul.a
    coe1tmmul.r
    coe1tmmul.c
    coe1tmmul.d
    coe1tmmul2
    fveq1d
    wph
    @10
    cD
    @0
    cle
    wbr
    #
    @0
    cD
    cmin
    co
    #
    @5
    cfv
    #
    cC
    c.xp
    co
    #
    c.0
    cif
    #
    @16
    @12
    wph
    @0
    cn0
    wcel
    @10
    @17
    wceq
    wph
    cD
    cY
    coe1tmmul.d
    coe1tmmul2fv.y
    nn0addcld
    vx
    @0
    @8
    @17
    cn0
    @9
    @2
    @0
    wceq
    #
    @3
    @13
    @7
    @16
    c.0
    @2
    @0
    cD
    cle
    breq2
    @18
    @6
    @15
    cC
    c.xp
    @18
    @4
    @14
    @5
    @2
    @0
    cD
    cmin
    oveq1
    fveq2d
    oveq1d
    ifbieq1d
    @9
    eqid
    @13
    @16
    c.0
    @15
    cC
    c.xp
    ovex
    c.0
    cR
    c0g
    cfv
    cvv
    coe1tm.z
    cR
    c0g
    fvex
    eqeltri
    ifex
    fvmpt
    syl
    wph
    @13
    @16
    c.0
    wph
    cD
    cr
    wcel
    cY
    cn0
    wcel
    @13
    wph
    cD
    coe1tmmul.d
    nn0red
    coe1tmmul2fv.y
    cD
    cY
    nn0addge1
    syl2anc
    iftrued
    wph
    @15
    @11
    cC
    c.xp
    wph
    @14
    cY
    @5
    wph
    cD
    cY
    wph
    cD
    coe1tmmul.d
    nn0cnd
    wph
    cY
    coe1tmmul2fv.y
    nn0cnd
    pncan2d
    fveq2d
    oveq1d
    3eqtrd
    eqtrd
end
