include "co.mm"
include "cfv.mm"
include "cmap.mm"
include "wcel.mm"
include "wf.mm"
include "cop.mm"
include "c1st.mm"
include "c2nd.mm"
include "df-ov.mm"
include "cxp.mm"
include "cv.mm"
include "cixp.mm"
include "funcixp.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "syl6eqr.mm"
include "fvixp.mm"
include "syl5eqel.mm"
include "wa.mm"
include "op1stg.mm"
include "op2ndg.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "elmapi.mm"
include "syl.mm"

theorem funcf2
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume funcixp.b: |- B = ( Base ` D )
  assume funcixp.h: |- H = ( Hom ` D )
  assume funcixp.j: |- J = ( Hom ` E )
  assume funcixp.f: |- ( ph -> F ( D Func E ) G )
  assume funcf2.x: |- ( ph -> X e. B )
  assume funcf2.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X G Y ) : ( X H Y ) --> ( ( F ` X ) J ( F ` Y ) ) )

  proof
    wph
    cX
    cY
    cG
    co
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cJ
    co
    #
    cX
    cY
    cH
    co
    #
    cmap
    co
    #
    wcel
    @4
    @3
    @0
    wf
    wph
    @0
    cX
    cY
    cop
    #
    c1st
    cfv
    #
    cF
    cfv
    #
    @6
    c2nd
    cfv
    #
    cF
    cfv
    #
    cJ
    co
    #
    @4
    cmap
    co
    #
    @5
    wph
    @0
    @6
    cG
    cfv
    #
    @12
    cX
    cY
    cG
    df-ov
    wph
    cG
    vz
    cB
    cB
    cxp
    #
    vz
    cv
    #
    c1st
    cfv
    #
    cF
    cfv
    #
    @15
    c2nd
    cfv
    #
    cF
    cfv
    #
    cJ
    co
    #
    @15
    cH
    cfv
    #
    cmap
    co
    #
    cixp
    wcel
    @6
    @14
    wcel
    #
    @13
    @12
    wcel
    wph
    vz
    cB
    cD
    cE
    cF
    cG
    cH
    cJ
    funcixp.b
    funcixp.h
    funcixp.j
    funcixp.f
    funcixp
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @23
    funcf2.x
    funcf2.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    vz
    @14
    @22
    @6
    @12
    cG
    @15
    @6
    wceq
    #
    @20
    @11
    @21
    @4
    cmap
    @26
    @17
    @8
    @19
    @10
    cJ
    @26
    @16
    @7
    cF
    @15
    @6
    c1st
    fveq2
    fveq2d
    @26
    @18
    @9
    cF
    @15
    @6
    c2nd
    fveq2
    fveq2d
    oveq12d
    @26
    @21
    @6
    cH
    cfv
    @4
    @15
    @6
    cH
    fveq2
    cX
    cY
    cH
    df-ov
    syl6eqr
    oveq12d
    fvixp
    syl2anc
    syl5eqel
    wph
    @11
    @3
    @4
    cmap
    wph
    @24
    @25
    @11
    @3
    wceq
    funcf2.x
    funcf2.y
    @24
    @25
    wa
    #
    @8
    @1
    @10
    @2
    cJ
    @27
    @7
    cX
    cF
    cX
    cY
    cB
    cB
    op1stg
    fveq2d
    @27
    @9
    cY
    cF
    cX
    cY
    cB
    cB
    op2ndg
    fveq2d
    oveq12d
    syl2anc
    oveq1d
    eleqtrd
    @0
    @3
    @4
    elmapi
    syl
end
