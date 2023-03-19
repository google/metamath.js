include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "c2nd.mm"
include "co.mm"
include "cvv.mm"
include "curf2.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "eqidd.mm"
include "fveq2d.mm"
include "oveq123d.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem curf2val
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vz: setvar z
  let vf: setvar f
  let vw: setvar w
  assume curf2.g: |- G = ( <. C , D >. curryF F )
  assume curf2.a: |- A = ( Base ` C )
  assume curf2.c: |- ( ph -> C e. Cat )
  assume curf2.d: |- ( ph -> D e. Cat )
  assume curf2.f: |- ( ph -> F e. ( ( C Xc. D ) Func E ) )
  assume curf2.b: |- B = ( Base ` D )
  assume curf2.h: |- H = ( Hom ` C )
  assume curf2.i: |- I = ( Id ` D )
  assume curf2.x: |- ( ph -> X e. A )
  assume curf2.y: |- ( ph -> Y e. A )
  assume curf2.k: |- ( ph -> K e. ( X H Y ) )
  assume curf2.l: |- L = ( ( X ( 2nd ` G ) Y ) ` K )
  assume curf2.z: |- ( ph -> Z e. B )


  assert |- ( ph -> ( L ` Z ) = ( K ( <. X , Z >. ( 2nd ` F ) <. Y , Z >. ) ( I ` Z ) ) )

  proof
    wph
    vz
    cZ
    cK
    vz
    cv
    #
    cI
    cfv
    #
    cX
    @0
    cop
    #
    cY
    @0
    cop
    #
    cF
    c2nd
    cfv
    #
    co
    #
    co
    cK
    cZ
    cI
    cfv
    #
    cX
    cZ
    cop
    #
    cY
    cZ
    cop
    #
    @4
    co
    #
    co
    cB
    cL
    cvv
    wph
    vz
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    cI
    cK
    cL
    cX
    cY
    curf2.g
    curf2.a
    curf2.c
    curf2.d
    curf2.f
    curf2.b
    curf2.h
    curf2.i
    curf2.x
    curf2.y
    curf2.k
    curf2.l
    curf2
    wph
    @0
    cZ
    wceq
    #
    wa
    #
    cK
    cK
    @1
    @6
    @5
    @9
    @11
    @2
    @7
    @3
    @8
    @4
    @11
    @0
    cZ
    cX
    wph
    @10
    simpr
    #
    opeq2d
    @11
    @0
    cZ
    cY
    @12
    opeq2d
    oveq12d
    @11
    cK
    eqidd
    @11
    @0
    cZ
    cI
    @12
    fveq2d
    oveq123d
    curf2.z
    wph
    cK
    @6
    @9
    ovexd
    fvmptd
end
