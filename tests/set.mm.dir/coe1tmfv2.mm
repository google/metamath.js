include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "crg.mm"
include "wcel.mm"
include "coe1tm.mm"
include "syl3anc.mm"
include "fveq1d.mm"
include "ring0cl.mm"
include "syl.mm"
include "ifcld.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "necomd.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "3eqtrd.mm"

theorem coe1tmfv2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.ex: class .^
  let cF: class F
  let cK: class K
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cY: class Y
  let c.xp: class .X.
  let c.xb: class .xb
  assume coe1tm.z: |- .0. = ( 0g ` R )
  assume coe1tm.k: |- K = ( Base ` R )
  assume coe1tm.p: |- P = ( Poly1 ` R )
  assume coe1tm.x: |- X = ( var1 ` R )
  assume coe1tm.m: |- .x. = ( .s ` P )
  assume coe1tm.n: |- N = ( mulGrp ` P )
  assume coe1tm.e: |- .^ = ( .g ` N )
  assume coe1tmfv2.r: |- ( ph -> R e. Ring )
  assume coe1tmfv2.c: |- ( ph -> C e. K )
  assume coe1tmfv2.d: |- ( ph -> D e. NN0 )
  assume coe1tmfv2.f: |- ( ph -> F e. NN0 )
  assume coe1tmfv2.q: |- ( ph -> D =/= F )


  assert |- ( ph -> ( ( coe1 ` ( C .x. ( D .^ X ) ) ) ` F ) = .0. )

  proof
    wph
    cF
    cC
    cD
    cX
    c.ex
    co
    c.x
    co
    cco1
    cfv
    #
    cfv
    cF
    vx
    cn0
    vx
    cv
    #
    cD
    wceq
    #
    cC
    c.0
    cif
    #
    cmpt
    #
    cfv
    #
    cF
    cD
    wceq
    #
    cC
    c.0
    cif
    #
    c.0
    wph
    cF
    @0
    @4
    wph
    cR
    crg
    wcel
    #
    cC
    cK
    wcel
    cD
    cn0
    wcel
    @0
    @4
    wceq
    coe1tmfv2.r
    coe1tmfv2.c
    coe1tmfv2.d
    vx
    cC
    cD
    cP
    cR
    c.x
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
    coe1tm
    syl3anc
    fveq1d
    wph
    cF
    cn0
    wcel
    @7
    cK
    wcel
    @5
    @7
    wceq
    coe1tmfv2.f
    wph
    @6
    cC
    c.0
    cK
    coe1tmfv2.c
    wph
    @8
    c.0
    cK
    wcel
    coe1tmfv2.r
    cK
    cR
    c.0
    coe1tm.k
    coe1tm.z
    ring0cl
    syl
    ifcld
    vx
    cF
    @3
    @7
    cn0
    cK
    @4
    @1
    cF
    wceq
    @2
    @6
    cC
    c.0
    @1
    cF
    cD
    eqeq1
    ifbid
    @4
    eqid
    fvmptg
    syl2anc
    wph
    @6
    cC
    c.0
    wph
    cF
    cD
    wph
    cD
    cF
    coe1tmfv2.q
    necomd
    neneqd
    iffalsed
    3eqtrd
end
