include "cop.mm"
include "cfv.mm"
include "co.mm"
include "df-ov.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "fveq2.mm"
include "opeq1d.mm"
include "opeq2d.mm"
include "cmpt2.mm"
include "cbvmpt2v.mm"
include "eqtri.mm"
include "opex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"
include "syl5eqr.mm"

theorem fvproj
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let vc: setvar c
  assume fvproj.h: |- H = ( x e. A , y e. B |-> <. ( F ` x ) , ( G ` y ) >. )
  assume fvproj.x: |- ( ph -> X e. A )
  assume fvproj.y: |- ( ph -> Y e. B )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint A a
  disjoint A b
  disjoint A z
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint x z
  disjoint y z
  disjoint B a
  disjoint B b
  disjoint B z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F z
  disjoint a c
  disjoint b c
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X z
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y z
  assert |- ( ph -> ( H ` <. X , Y >. ) = <. ( F ` X ) , ( G ` Y ) >. )

  proof
    wph
    cX
    cY
    cop
    cH
    cfv
    cX
    cY
    cH
    co
    #
    cX
    cF
    cfv
    #
    cY
    cG
    cfv
    #
    cop
    #
    cX
    cY
    cH
    df-ov
    wph
    cX
    cA
    wcel
    cY
    cB
    wcel
    @0
    @3
    wceq
    fvproj.x
    fvproj.y
    va
    vb
    cX
    cY
    cA
    cB
    va
    cv
    #
    cF
    cfv
    #
    vb
    cv
    #
    cG
    cfv
    #
    cop
    #
    @3
    cH
    @1
    @7
    cop
    @4
    cX
    wceq
    @5
    @1
    @7
    @4
    cX
    cF
    fveq2
    opeq1d
    @6
    cY
    wceq
    @7
    @2
    @1
    @6
    cY
    cG
    fveq2
    opeq2d
    cH
    vx
    vy
    cA
    cB
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cG
    cfv
    #
    cop
    #
    cmpt2
    va
    vb
    cA
    cB
    @8
    cmpt2
    fvproj.h
    vx
    vy
    va
    vb
    cA
    cB
    @13
    @8
    @5
    @12
    cop
    @9
    @4
    wceq
    @10
    @5
    @12
    @9
    @4
    cF
    fveq2
    opeq1d
    @11
    @6
    wceq
    @12
    @7
    @5
    @11
    @6
    cG
    fveq2
    opeq2d
    cbvmpt2v
    eqtri
    @1
    @2
    opex
    ovmpt2
    syl2anc
    syl5eqr
end
