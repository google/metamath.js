include "cc0.mm"
include "wne.mm"
include "cc.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "quartlem3.mm"
include "simp2d.mm"
include "sqrtcld.mm"
include "2cnd.mm"
include "cexp.mm"
include "sqsqrtd.mm"
include "eqnetrd.mm"
include "wb.mm"
include "sqne0.mm"
include "syl.mm"
include "mpbid.mm"
include "2ne0.mm"
include "a1i.mm"
include "divne0d.mm"
include "cneg.mm"
include "cmin.mm"
include "c4.mm"
include "caddc.mm"
include "simp1d.mm"
include "sqcld.mm"
include "negcld.mm"
include "quart1cl.mm"
include "halfcld.mm"
include "subcld.mm"
include "4cn.mm"
include "4ne0.mm"
include "divcld.mm"
include "addcld.mm"
include "eqeltrd.mm"
include "3jca.mm"

theorem quartlem4
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cI: class I
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume quart.a: |- ( ph -> A e. CC )
  assume quart.b: |- ( ph -> B e. CC )
  assume quart.c: |- ( ph -> C e. CC )
  assume quart.d: |- ( ph -> D e. CC )
  assume quart.x: |- ( ph -> X e. CC )
  assume quart.e: |- ( ph -> E = -u ( A / 4 ) )
  assume quart.p: |- ( ph -> P = ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) )
  assume quart.q: |- ( ph -> Q = ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) )
  assume quart.r: |- ( ph -> R = ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) )
  assume quart.u: |- ( ph -> U = ( ( P ^ 2 ) + ( ; 1 2 x. R ) ) )
  assume quart.v: |- ( ph -> V = ( ( -u ( 2 x. ( P ^ 3 ) ) - ( ; 2 7 x. ( Q ^ 2 ) ) ) + ( ; 7 2 x. ( P x. R ) ) ) )
  assume quart.w: |- ( ph -> W = ( sqrt ` ( ( V ^ 2 ) - ( 4 x. ( U ^ 3 ) ) ) ) )
  assume quart.s: |- ( ph -> S = ( ( sqrt ` M ) / 2 ) )
  assume quart.m: |- ( ph -> M = -u ( ( ( ( 2 x. P ) + T ) + ( U / T ) ) / 3 ) )
  assume quart.t: |- ( ph -> T = ( ( ( V + W ) / 2 ) ^c ( 1 / 3 ) ) )
  assume quart.t0: |- ( ph -> T =/= 0 )
  assume quart.m0: |- ( ph -> M =/= 0 )
  assume quart.i: |- ( ph -> I = ( sqrt ` ( ( -u ( S ^ 2 ) - ( P / 2 ) ) + ( ( Q / 4 ) / S ) ) ) )
  assume quart.j: |- ( ph -> J = ( sqrt ` ( ( -u ( S ^ 2 ) - ( P / 2 ) ) - ( ( Q / 4 ) / S ) ) ) )


  assert |- ( ph -> ( S =/= 0 /\ I e. CC /\ J e. CC ) )

  proof
    wph
    cS
    cc0
    wne
    cI
    cc
    wcel
    cJ
    cc
    wcel
    wph
    cS
    cM
    csqrt
    cfv
    #
    c2
    cdiv
    co
    cc0
    quart.s
    wph
    @0
    c2
    wph
    cM
    wph
    cS
    cc
    wcel
    #
    cM
    cc
    wcel
    #
    cT
    cc
    wcel
    #
    wph
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cE
    cM
    cV
    cW
    cA
    quart.a
    quart.b
    quart.c
    quart.d
    quart.a
    quart.e
    quart.p
    quart.q
    quart.r
    quart.u
    quart.v
    quart.w
    quart.s
    quart.m
    quart.t
    quart.t0
    quartlem3
    #
    simp2d
    #
    sqrtcld
    #
    wph
    2cnd
    wph
    @0
    c2
    cexp
    co
    #
    cc0
    wne
    #
    @0
    cc0
    wne
    #
    wph
    @7
    cM
    cc0
    wph
    cM
    @5
    sqsqrtd
    quart.m0
    eqnetrd
    wph
    @0
    cc
    wcel
    @8
    @9
    wb
    @6
    @0
    sqne0
    syl
    mpbid
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    divne0d
    eqnetrd
    #
    wph
    cI
    cS
    c2
    cexp
    co
    #
    cneg
    #
    cP
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cQ
    c4
    cdiv
    co
    #
    cS
    cdiv
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    cc
    quart.i
    wph
    @17
    wph
    @14
    @16
    wph
    @12
    @13
    wph
    @11
    wph
    cS
    wph
    @1
    @2
    @3
    @4
    simp1d
    #
    sqcld
    negcld
    wph
    cP
    wph
    cP
    cc
    wcel
    #
    cQ
    cc
    wcel
    #
    cR
    cc
    wcel
    #
    wph
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    quart.a
    quart.b
    quart.c
    quart.d
    quart.p
    quart.q
    quart.r
    quart1cl
    #
    simp1d
    halfcld
    subcld
    #
    wph
    @15
    cS
    wph
    cQ
    c4
    wph
    @19
    @20
    @21
    @22
    simp2d
    c4
    cc
    wcel
    wph
    4cn
    a1i
    c4
    cc0
    wne
    wph
    4ne0
    a1i
    divcld
    @18
    @10
    divcld
    #
    addcld
    sqrtcld
    eqeltrd
    wph
    cJ
    @14
    @16
    cmin
    co
    #
    csqrt
    cfv
    cc
    quart.j
    wph
    @25
    wph
    @14
    @16
    @23
    @24
    subcld
    sqrtcld
    eqeltrd
    3jca
end
