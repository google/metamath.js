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
include "cfil.mm"
include "crab.mm"
include "wa.mm"
include "cfilfval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "rexeq.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem iscfil
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  let vr: setvar r
  let cG: class G
  let cJ: class J
  let cR: class R
  let cY: class Y
  let vd: setvar d

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X x
  disjoint X y
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
  disjoint f x
  disjoint f y
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
  disjoint F z
  disjoint X f
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
  disjoint D f
  disjoint D r
  disjoint D s
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  assert |- ( D e. ( *Met ` X ) -> ( F e. ( CauFil ` D ) <-> ( F e. ( Fil ` X ) /\ A. x e. RR+ E. y e. F ( D " ( y X. y ) ) C_ ( 0 [,) x ) ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cF
    cD
    ccfil
    cfv
    #
    wcel
    cF
    cD
    vy
    cv
    #
    @2
    cxp
    cima
    cc0
    vx
    cv
    cico
    co
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
    cX
    cfil
    cfv
    #
    crab
    #
    wcel
    cF
    @7
    wcel
    @3
    vy
    cF
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @0
    @1
    @8
    cF
    vx
    vy
    cD
    vf
    cX
    cfilfval
    eleq2d
    @6
    @10
    vf
    cF
    @7
    @4
    cF
    wceq
    @5
    @9
    vx
    crp
    @3
    vy
    @4
    cF
    rexeq
    ralbidv
    elrab
    syl6bb
end
