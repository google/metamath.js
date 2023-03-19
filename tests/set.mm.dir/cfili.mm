include "ccfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cdm.mm"
include "cfil.mm"
include "wa.mm"
include "cxmt.mm"
include "wb.mm"
include "crn.mm"
include "cuni.mm"
include "cxp.mm"
include "cima.mm"
include "cc0.mm"
include "cico.mm"
include "wss.mm"
include "crab.mm"
include "df-cfil.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "xmetunirn.mm"
include "sylib.mm"
include "iscfil2.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"
include "wceq.mm"
include "breq2.mm"
include "2ralbidv.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "sylan.mm"

theorem cfili
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cR: class R
  let cF: class F
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cB: class B
  let vf: setvar f
  let vr: setvar r
  let cX: class X
  let cG: class G
  let cJ: class J
  let cY: class Y
  let vd: setvar d

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint D x
  disjoint D y
  disjoint D z
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
  disjoint B x
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
  disjoint X f
  disjoint X r
  disjoint X s
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint G x
  disjoint G y
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint R r
  disjoint R s
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
  assert |- ( ( F e. ( CauFil ` D ) /\ R e. RR+ ) -> E. x e. F A. y e. x A. z e. x ( y D z ) < R )

  proof
    cF
    cD
    ccfil
    cfv
    wcel
    #
    vy
    cv
    #
    vz
    cv
    cD
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    vz
    vx
    cv
    #
    wral
    vy
    @5
    wral
    #
    vx
    cF
    wrex
    #
    vr
    crp
    wral
    #
    cR
    crp
    wcel
    @2
    cR
    clt
    wbr
    #
    vz
    @5
    wral
    vy
    @5
    wral
    #
    vx
    cF
    wrex
    #
    @0
    cF
    cD
    cdm
    cdm
    #
    cfil
    cfv
    wcel
    #
    @8
    @0
    @13
    @8
    wa
    #
    @0
    cD
    @12
    cxmt
    cfv
    wcel
    #
    @0
    @14
    wb
    @0
    cD
    cxmt
    crn
    cuni
    #
    wcel
    @15
    @0
    ccfil
    cdm
    @16
    cD
    vd
    @16
    vd
    cv
    #
    @1
    @1
    cxp
    cima
    cc0
    @5
    cico
    co
    wss
    vy
    vf
    cv
    wrex
    vx
    crp
    wral
    vf
    @17
    cdm
    cdm
    cfil
    cfv
    crab
    ccfil
    vx
    vy
    vf
    vd
    df-cfil
    dmmptss
    cF
    cD
    ccfil
    elfvdm
    sseldi
    cD
    xmetunirn
    sylib
    vr
    vx
    vy
    vz
    cD
    cF
    @12
    iscfil2
    syl
    ibi
    simprd
    @7
    @11
    vr
    cR
    crp
    @3
    cR
    wceq
    #
    @6
    @10
    vx
    cF
    @18
    @4
    @9
    vy
    vz
    @5
    @5
    @3
    cR
    @2
    clt
    breq2
    2ralbidv
    rexbidv
    rspccva
    sylan
end
