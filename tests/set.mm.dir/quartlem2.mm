include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cdc.mm"
include "cmul.mm"
include "caddc.mm"
include "quart1cl.mm"
include "simp1d.mm"
include "sqcld.mm"
include "1nn0.mm"
include "2nn.mm"
include "decnncl.mm"
include "nncni.mm"
include "simp3d.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcld.mm"
include "eqeltrd.mm"
include "c3.mm"
include "cneg.mm"
include "c7.mm"
include "cmin.mm"
include "2cn.mm"
include "cn0.mm"
include "3nn0.mm"
include "expcl.mm"
include "sylancl.mm"
include "negcld.mm"
include "2nn0.mm"
include "7nn.mm"
include "simp2d.mm"
include "subcld.mm"
include "7nn0.mm"
include "mulcld.mm"
include "c4.mm"
include "csqrt.mm"
include "cfv.mm"
include "4cn.mm"
include "sqrtcld.mm"
include "3jca.mm"

theorem quartlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X
  let cM: class M
  let vx: setvar x
  let cT: class T
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


  assert |- ( ph -> ( U e. CC /\ V e. CC /\ W e. CC ) )

  proof
    wph
    cU
    cc
    wcel
    #
    cV
    cc
    wcel
    cW
    cc
    wcel
    wph
    cU
    cP
    c2
    cexp
    co
    #
    c1
    c2
    cdc
    #
    cR
    cmul
    co
    #
    caddc
    co
    cc
    quart.u
    wph
    @1
    @3
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
    #
    sqcld
    wph
    @2
    cc
    wcel
    @6
    @3
    cc
    wcel
    @2
    c1
    c2
    1nn0
    2nn
    decnncl
    nncni
    wph
    @4
    @5
    @6
    @7
    simp3d
    #
    @2
    cR
    mulcl
    sylancr
    addcld
    eqeltrd
    #
    wph
    cV
    c2
    cP
    c3
    cexp
    co
    #
    cmul
    co
    #
    cneg
    #
    c2
    c7
    cdc
    #
    cQ
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c7
    c2
    cdc
    #
    cP
    cR
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    cc
    quart.v
    wph
    @17
    @20
    wph
    @13
    @16
    wph
    @12
    wph
    c2
    cc
    wcel
    @11
    cc
    wcel
    #
    @12
    cc
    wcel
    2cn
    wph
    @4
    c3
    cn0
    wcel
    #
    @21
    @8
    3nn0
    cP
    c3
    expcl
    sylancl
    c2
    @11
    mulcl
    sylancr
    negcld
    wph
    @14
    cc
    wcel
    @15
    cc
    wcel
    @16
    cc
    wcel
    @14
    c2
    c7
    2nn0
    7nn
    decnncl
    nncni
    wph
    cQ
    wph
    @4
    @5
    @6
    @7
    simp2d
    sqcld
    @14
    @15
    mulcl
    sylancr
    subcld
    wph
    @18
    cc
    wcel
    @19
    cc
    wcel
    @20
    cc
    wcel
    @18
    c7
    c2
    7nn0
    2nn
    decnncl
    nncni
    wph
    cP
    cR
    @8
    @9
    mulcld
    @18
    @19
    mulcl
    sylancr
    addcld
    eqeltrd
    #
    wph
    cW
    cV
    c2
    cexp
    co
    #
    c4
    cU
    c3
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    cc
    quart.w
    wph
    @27
    wph
    @24
    @26
    wph
    cV
    @23
    sqcld
    wph
    c4
    cc
    wcel
    @25
    cc
    wcel
    #
    @26
    cc
    wcel
    4cn
    wph
    @0
    @22
    @28
    @10
    3nn0
    cU
    c3
    expcl
    sylancl
    c4
    @25
    mulcl
    sylancr
    subcld
    sqrtcld
    eqeltrd
    3jca
end
