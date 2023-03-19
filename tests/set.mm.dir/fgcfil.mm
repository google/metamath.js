include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
include "wa.mm"
include "cfg.mm"
include "co.mm"
include "ccfil.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cfili.mm"
include "adantll.mm"
include "wss.mm"
include "wi.mm"
include "wb.mm"
include "elfg.mm"
include "ad3antlr.mm"
include "ssralv.mm"
include "ralimdv.mm"
include "syldc.mm"
include "reximdv.mm"
include "com12.mm"
include "adantl.mm"
include "syl6bi.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "ex.mm"
include "cfil.mm"
include "ssfg.mm"
include "ssrexv.mm"
include "syl.mm"
include "fgcl.mm"
include "jctild.mm"
include "iscfil2.mm"
include "adantr.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem fgcfil
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cD: class D
  let cX: class X
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vf: setvar f
  let vr: setvar r
  let cF: class F
  let cG: class G
  let cJ: class J
  let cR: class R
  let cY: class Y
  let vd: setvar d

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint D w
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
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint X f
  disjoint X r
  disjoint X s
  disjoint X u
  disjoint X v
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
  assert |- ( ( D e. ( *Met ` X ) /\ B e. ( fBas ` X ) ) -> ( ( X filGen B ) e. ( CauFil ` D ) <-> A. x e. RR+ E. y e. B A. z e. y A. w e. y ( z D w ) < x ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cB
    cX
    cfbas
    cfv
    wcel
    #
    wa
    #
    cX
    cB
    cfg
    co
    #
    cD
    ccfil
    cfv
    wcel
    #
    vz
    cv
    vw
    cv
    cD
    co
    vx
    cv
    #
    clt
    wbr
    #
    vw
    vy
    cv
    #
    wral
    #
    vz
    @7
    wral
    #
    vy
    cB
    wrex
    #
    vx
    crp
    wral
    #
    @2
    @4
    @11
    @2
    @4
    wa
    #
    @10
    vx
    crp
    @12
    @5
    crp
    wcel
    #
    wa
    #
    @6
    vw
    vu
    cv
    #
    wral
    #
    vz
    @15
    wral
    #
    vu
    @3
    wrex
    #
    @10
    @4
    @13
    @18
    @2
    vu
    vz
    vw
    cD
    @5
    @3
    cfili
    adantll
    @14
    @17
    @10
    vu
    @3
    @14
    @15
    @3
    wcel
    #
    @15
    cX
    wss
    #
    @7
    @15
    wss
    #
    vy
    cB
    wrex
    #
    wa
    #
    @17
    @10
    wi
    #
    @1
    @19
    @23
    wb
    @0
    @4
    @13
    vy
    @15
    cB
    cX
    elfg
    ad3antlr
    @22
    @24
    @20
    @17
    @22
    @10
    @17
    @21
    @9
    vy
    cB
    @21
    @17
    @8
    vz
    @15
    wral
    @9
    @21
    @16
    @8
    vz
    @15
    @6
    vw
    @7
    @15
    ssralv
    ralimdv
    @8
    vz
    @7
    @15
    ssralv
    syldc
    reximdv
    com12
    adantl
    syl6bi
    rexlimdv
    mpd
    ralrimiva
    ex
    @2
    @11
    @3
    cX
    cfil
    cfv
    wcel
    #
    @9
    vy
    @3
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    @4
    @2
    @11
    @27
    @25
    @2
    cB
    @3
    wss
    #
    @11
    @27
    wi
    @1
    @29
    @0
    cB
    cX
    ssfg
    adantl
    @29
    @10
    @26
    vx
    crp
    @9
    vy
    cB
    @3
    ssrexv
    ralimdv
    syl
    @1
    @25
    @0
    cB
    cX
    fgcl
    adantl
    jctild
    @0
    @4
    @28
    wb
    @1
    vx
    vy
    vz
    vw
    cD
    @3
    cX
    iscfil2
    adantr
    sylibrd
    impbid
end
