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
include "coe1pwmul.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "nn0addcld.mm"
include "breq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "ifbieq1d.mm"
include "eqid.mm"
include "fvex.mm"
include "c0g.mm"
include "cvv.mm"
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

theorem coe1pwmulfv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.ex: class .^
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  assume coe1pwmul.z: |- .0. = ( 0g ` R )
  assume coe1pwmul.p: |- P = ( Poly1 ` R )
  assume coe1pwmul.x: |- X = ( var1 ` R )
  assume coe1pwmul.n: |- N = ( mulGrp ` P )
  assume coe1pwmul.e: |- .^ = ( .g ` N )
  assume coe1pwmul.b: |- B = ( Base ` P )
  assume coe1pwmul.t: |- .x. = ( .r ` P )
  assume coe1pwmul.r: |- ( ph -> R e. Ring )
  assume coe1pwmul.a: |- ( ph -> A e. B )
  assume coe1pwmul.d: |- ( ph -> D e. NN0 )
  assume coe1pwmulfv.y: |- ( ph -> Y e. NN0 )


  assert |- ( ph -> ( ( coe1 ` ( ( D .^ X ) .x. A ) ) ` ( D + Y ) ) = ( ( coe1 ` A ) ` Y ) )

  proof
    wph
    cD
    cY
    caddc
    co
    #
    cD
    cX
    c.ex
    co
    cA
    c.x
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
    wph
    @0
    @1
    @8
    wph
    vx
    cA
    cB
    cD
    cP
    cR
    c.x
    c.ex
    cN
    cX
    c.0
    coe1pwmul.z
    coe1pwmul.p
    coe1pwmul.x
    coe1pwmul.n
    coe1pwmul.e
    coe1pwmul.b
    coe1pwmul.t
    coe1pwmul.r
    coe1pwmul.a
    coe1pwmul.d
    coe1pwmul
    fveq1d
    wph
    @9
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
    c.0
    cif
    #
    @13
    @10
    wph
    @0
    cn0
    wcel
    @9
    @14
    wceq
    wph
    cD
    cY
    coe1pwmul.d
    coe1pwmulfv.y
    nn0addcld
    vx
    @0
    @7
    @14
    cn0
    @8
    @2
    @0
    wceq
    #
    @3
    @11
    @6
    @13
    c.0
    @2
    @0
    cD
    cle
    breq2
    @15
    @4
    @12
    @5
    @2
    @0
    cD
    cmin
    oveq1
    fveq2d
    ifbieq1d
    @8
    eqid
    @11
    @13
    c.0
    @12
    @5
    fvex
    c.0
    cR
    c0g
    cfv
    cvv
    coe1pwmul.z
    cR
    c0g
    fvex
    eqeltri
    ifex
    fvmpt
    syl
    wph
    @11
    @13
    c.0
    wph
    cD
    cr
    wcel
    cY
    cn0
    wcel
    @11
    wph
    cD
    coe1pwmul.d
    nn0red
    coe1pwmulfv.y
    cD
    cY
    nn0addge1
    syl2anc
    iftrued
    wph
    @12
    cY
    @5
    wph
    cD
    cY
    wph
    cD
    coe1pwmul.d
    nn0cnd
    wph
    cY
    coe1pwmulfv.y
    nn0cnd
    pncan2d
    fveq2d
    3eqtrd
    eqtrd
end
