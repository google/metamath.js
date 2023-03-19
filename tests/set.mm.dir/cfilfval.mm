include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ccfil.mm"
include "cv.mm"
include "cxp.mm"
include "cima.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "wss.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "cdm.mm"
include "cfil.mm"
include "crab.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "dmeq.mm"
include "dmeqd.mm"
include "fveq2d.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "df-cfil.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl.mm"
include "xmetdmdm.mm"
include "rabeq.mm"
include "eqtr4d.mm"

theorem cfilfval
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let vf: setvar f
  let cX: class X
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let vr: setvar r
  let cF: class F
  let cG: class G
  let cJ: class J
  let cR: class R
  let cY: class Y
  let vd: setvar d

  disjoint x y
  disjoint f x
  disjoint f y
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint D f
  disjoint D x
  disjoint D y
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint f r
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f z
  disjoint F f
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint X r
  disjoint X s
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint G x
  disjoint G y
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint R r
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint d f
  disjoint d r
  disjoint d s
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint D r
  disjoint D s
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  assert |- ( D e. ( *Met ` X ) -> ( CauFil ` D ) = { f e. ( Fil ` X ) | A. x e. RR+ E. y e. f ( D " ( y X. y ) ) C_ ( 0 [,) x ) } )

  proof
    cD
    cX
    cxmt
    cfv
    #
    wcel
    #
    cD
    ccfil
    cfv
    #
    cD
    vy
    cv
    #
    @3
    cxp
    #
    cima
    #
    cc0
    vx
    cv
    cico
    co
    #
    wss
    #
    vy
    vf
    cv
    #
    wrex
    #
    vx
    crp
    wral
    #
    vf
    cD
    cdm
    #
    cdm
    #
    cfil
    cfv
    #
    crab
    #
    @10
    vf
    cX
    cfil
    cfv
    #
    crab
    #
    @1
    cD
    cxmt
    crn
    cuni
    #
    wcel
    @2
    @14
    wceq
    @0
    @17
    cD
    cxmt
    cX
    fvssunirn
    sseli
    vd
    cD
    vd
    cv
    #
    @4
    cima
    #
    @6
    wss
    #
    vy
    @8
    wrex
    #
    vx
    crp
    wral
    #
    vf
    @18
    cdm
    #
    cdm
    #
    cfil
    cfv
    #
    crab
    @14
    @17
    ccfil
    @18
    cD
    wceq
    #
    @22
    @10
    vf
    @25
    @13
    @26
    @24
    @12
    cfil
    @26
    @23
    @11
    @18
    cD
    dmeq
    dmeqd
    fveq2d
    @26
    @21
    @9
    vx
    crp
    @26
    @20
    @7
    vy
    @8
    @26
    @19
    @5
    @6
    @18
    cD
    @4
    imaeq1
    sseq1d
    rexbidv
    ralbidv
    rabeqbidv
    vx
    vy
    vf
    vd
    df-cfil
    @10
    vf
    @13
    @12
    cfil
    fvex
    rabex
    fvmpt
    syl
    @1
    @15
    @13
    wceq
    @16
    @14
    wceq
    @1
    cX
    @12
    cfil
    cD
    cX
    xmetdmdm
    fveq2d
    @10
    vf
    @15
    @13
    rabeq
    syl
    eqtr4d
end
