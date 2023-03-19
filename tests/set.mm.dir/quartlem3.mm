include "cc.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "c3.mm"
include "cneg.mm"
include "2cn.mm"
include "quart1cl.mm"
include "simp1d.mm"
include "mulcl.mm"
include "sylancr.mm"
include "c1.mm"
include "ccxp.mm"
include "quartlem2.mm"
include "simp2d.mm"
include "simp3d.mm"
include "addcld.mm"
include "halfcld.mm"
include "cn.mm"
include "cr.mm"
include "3nn.mm"
include "nnrecre.mm"
include "ax-mp.mm"
include "recni.mm"
include "cxpcl.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "divcld.mm"
include "3cn.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "3ne0.mm"
include "negcld.mm"
include "sqrtcld.mm"
include "3jca.mm"

theorem quartlem3
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


  assert |- ( ph -> ( S e. CC /\ M e. CC /\ T e. CC ) )

  proof
    wph
    cS
    cc
    wcel
    cM
    cc
    wcel
    cT
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
    cc
    quart.s
    wph
    @0
    wph
    cM
    wph
    cM
    c2
    cP
    cmul
    co
    #
    cT
    caddc
    co
    #
    cU
    cT
    cdiv
    co
    #
    caddc
    co
    #
    c3
    cdiv
    co
    #
    cneg
    cc
    quart.m
    wph
    @5
    wph
    @4
    c3
    wph
    @2
    @3
    wph
    @1
    cT
    wph
    c2
    cc
    wcel
    cP
    cc
    wcel
    #
    @1
    cc
    wcel
    2cn
    wph
    @6
    cQ
    cc
    wcel
    cR
    cc
    wcel
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
    simp1d
    c2
    cP
    mulcl
    sylancr
    wph
    cT
    cV
    cW
    caddc
    co
    #
    c2
    cdiv
    co
    #
    c1
    c3
    cdiv
    co
    #
    ccxp
    co
    #
    cc
    quart.t
    wph
    @8
    cc
    wcel
    @9
    cc
    wcel
    @10
    cc
    wcel
    wph
    @7
    wph
    cV
    cW
    wph
    cU
    cc
    wcel
    #
    cV
    cc
    wcel
    #
    cW
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
    cU
    cE
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
    quartlem2
    #
    simp2d
    wph
    @11
    @12
    @13
    @14
    simp3d
    addcld
    halfcld
    @9
    c3
    cn
    wcel
    @9
    cr
    wcel
    3nn
    c3
    nnrecre
    ax-mp
    recni
    @8
    @9
    cxpcl
    sylancl
    eqeltrd
    #
    addcld
    wph
    cU
    cT
    wph
    @11
    @12
    @13
    @14
    simp1d
    @15
    quart.t0
    divcld
    addcld
    c3
    cc
    wcel
    wph
    3cn
    a1i
    c3
    cc0
    wne
    wph
    3ne0
    a1i
    divcld
    negcld
    eqeltrd
    #
    sqrtcld
    halfcld
    eqeltrd
    @16
    @15
    3jca
end
