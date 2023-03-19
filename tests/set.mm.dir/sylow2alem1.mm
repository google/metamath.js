include "wcel.mm"
include "wa.mm"
include "cec.mm"
include "csn.mm"
include "cv.mm"
include "wceq.mm"
include "wbr.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "simpr.mm"
include "elecg.mm"
include "sylancr.mm"
include "co.mm"
include "wrex.mm"
include "gaorb.mm"
include "simp3bi.mm"
include "wral.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "sylib.mm"
include "simprd.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "eqeq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "sylbid.mm"
include "velsn.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "wer.mm"
include "cga.mm"
include "gaorber.mm"
include "syl.mm"
include "adantr.mm"
include "simpld.mm"
include "erref.mm"
include "sylancom.mm"
include "mpbird.mm"
include "snssd.mm"
include "eqssd.mm"

theorem sylow2alem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cP: class P
  let c.po: class .(+)
  let c.sm: class .~
  let vg: setvar g
  let vh: setvar h
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  let vn: setvar n
  let vw: setvar w
  let vz: setvar z
  let vv: setvar v
  assume sylow2a.x: |- X = ( Base ` G )
  assume sylow2a.m: |- ( ph -> .(+) e. ( G GrpAct Y ) )
  assume sylow2a.p: |- ( ph -> P pGrp G )
  assume sylow2a.f: |- ( ph -> X e. Fin )
  assume sylow2a.y: |- ( ph -> Y e. Fin )
  assume sylow2a.z: |- Z = { u e. Y | A. h e. X ( h .(+) u ) = u }
  assume sylow2a.r: |- .~ = { <. x , y >. | ( { x , y } C_ Y /\ E. g e. X ( g .(+) x ) = y ) }

  disjoint .~ h
  disjoint g h
  disjoint g u
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint h u
  disjoint h x
  disjoint h y
  disjoint A h
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint G g
  disjoint G x
  disjoint G y
  disjoint .(+) g
  disjoint .(+) h
  disjoint .(+) u
  disjoint .(+) x
  disjoint .(+) y
  disjoint X g
  disjoint X h
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint h ph
  disjoint Y g
  disjoint Y h
  disjoint Y u
  disjoint Y x
  disjoint Y y
  disjoint h k
  disjoint h n
  disjoint h w
  disjoint h z
  disjoint k n
  disjoint k w
  disjoint k z
  disjoint .~ k
  disjoint n w
  disjoint n z
  disjoint .~ n
  disjoint w z
  disjoint .~ w
  disjoint .~ z
  disjoint g k
  disjoint g w
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint u w
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint g n
  disjoint g v
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint G n
  disjoint v x
  disjoint v y
  disjoint G v
  disjoint P n
  disjoint P w
  disjoint P z
  disjoint v w
  disjoint h v
  disjoint k v
  disjoint .(+) k
  disjoint u v
  disjoint .(+) v
  disjoint X k
  disjoint n u
  disjoint X n
  disjoint X v
  disjoint Z k
  disjoint Z w
  disjoint Z z
  disjoint k ph
  disjoint ph w
  disjoint ph z
  disjoint g z
  disjoint Y k
  disjoint u z
  disjoint Y w
  disjoint x z
  disjoint y z
  disjoint Y z
  assert |- ( ( ph /\ A e. Z ) -> [ A ] .~ = { A } )

  proof
    wph
    cA
    cZ
    wcel
    #
    wa
    #
    cA
    c.sm
    cec
    #
    cA
    csn
    #
    @1
    vw
    @2
    @3
    @1
    vw
    cv
    #
    @2
    wcel
    #
    @4
    cA
    wceq
    #
    @4
    @3
    wcel
    @1
    @5
    cA
    @4
    c.sm
    wbr
    #
    @6
    @1
    @4
    cvv
    wcel
    @0
    @5
    @7
    wb
    vw
    vex
    wph
    @0
    simpr
    #
    @4
    cA
    c.sm
    cvv
    cZ
    elecg
    sylancr
    @7
    vk
    cv
    #
    cA
    c.po
    co
    #
    @4
    wceq
    #
    vk
    cX
    wrex
    #
    @1
    @6
    @7
    cA
    cY
    wcel
    #
    @4
    cY
    wcel
    @12
    vx
    vy
    cA
    @4
    c.po
    c.sm
    vg
    vk
    cX
    cY
    sylow2a.r
    gaorb
    simp3bi
    @1
    @11
    @6
    vk
    cX
    @1
    @9
    cX
    wcel
    #
    wa
    @10
    cA
    wceq
    #
    @11
    @6
    @1
    vh
    cv
    #
    cA
    c.po
    co
    #
    cA
    wceq
    #
    vh
    cX
    wral
    #
    @14
    @15
    @1
    @13
    @19
    @1
    @0
    @13
    @19
    wa
    @8
    @16
    vu
    cv
    #
    c.po
    co
    #
    @20
    wceq
    #
    vh
    cX
    wral
    @19
    vu
    cA
    cY
    cZ
    @20
    cA
    wceq
    #
    @22
    @18
    vh
    cX
    @23
    @21
    @17
    @20
    cA
    @20
    cA
    @16
    c.po
    oveq2
    @23
    id
    eqeq12d
    ralbidv
    sylow2a.z
    elrab2
    sylib
    #
    simprd
    @18
    @15
    vh
    @9
    cX
    @16
    @9
    wceq
    @17
    @10
    cA
    @16
    @9
    cA
    c.po
    oveq1
    eqeq1d
    rspccva
    sylan
    @10
    @4
    cA
    eqeq1
    syl5ibcom
    rexlimdva
    syl5
    sylbid
    vw
    cA
    velsn
    syl6ibr
    ssrdv
    @1
    cA
    @2
    @1
    cA
    @2
    wcel
    #
    cA
    cA
    c.sm
    wbr
    #
    @1
    cA
    c.sm
    cY
    wph
    cY
    c.sm
    wer
    #
    @0
    wph
    c.po
    cG
    cY
    cga
    co
    wcel
    @27
    sylow2a.m
    vx
    vy
    c.po
    c.sm
    vg
    cG
    cX
    cY
    sylow2a.r
    sylow2a.x
    gaorber
    syl
    adantr
    @1
    @13
    @19
    @24
    simpld
    erref
    wph
    @0
    @0
    @25
    @26
    wb
    @8
    cA
    cA
    c.sm
    cZ
    cZ
    elecg
    sylancom
    mpbird
    snssd
    eqssd
end
