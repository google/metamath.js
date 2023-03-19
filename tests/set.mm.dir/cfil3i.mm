include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ccfil.mm"
include "crp.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cbl.mm"
include "cfili.mm"
include "3adant1.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "cfil.mm"
include "cfilfil.mm"
include "3adant3.mm"
include "fileln0.mm"
include "sylan.mm"
include "r19.2z.mm"
include "ex.mm"
include "syl.mm"
include "wss.mm"
include "filelss.mm"
include "ssrexv.mm"
include "dfss3.mm"
include "cxr.mm"
include "wb.mm"
include "simpl1.mm"
include "ad2antrr.mm"
include "simpll3.mm"
include "rpxrd.mm"
include "adantr.mm"
include "simplr.mm"
include "sselda.mm"
include "elbl2.mm"
include "syl22anc.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "simpr.mm"
include "blssm.mm"
include "syl3anc.mm"
include "filss.mm"
include "3exp2.mm"
include "syl3c.mm"
include "sylbird.mm"
include "reximdva.mm"
include "3syld.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem cfil3i
  let vx: setvar x
  let cD: class D
  let cR: class R
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  let vr: setvar r
  let cG: class G
  let cJ: class J
  let cY: class Y
  let vd: setvar d

  disjoint F x
  disjoint X x
  disjoint R x
  disjoint D x
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
  disjoint x y
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
  disjoint F y
  disjoint F z
  disjoint X f
  disjoint X r
  disjoint X s
  disjoint X u
  disjoint X v
  disjoint X w
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
  disjoint D y
  disjoint D z
  assert |- ( ( D e. ( *Met ` X ) /\ F e. ( CauFil ` D ) /\ R e. RR+ ) -> E. x e. X ( x ( ball ` D ) R ) e. F )

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
    wcel
    #
    cR
    crp
    wcel
    #
    w3a
    #
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    cR
    clt
    wbr
    #
    vy
    vs
    cv
    #
    wral
    #
    vx
    @7
    wral
    #
    vs
    cF
    wrex
    #
    @4
    cR
    cD
    cbl
    cfv
    co
    #
    cF
    wcel
    #
    vx
    cX
    wrex
    #
    @1
    @2
    @10
    @0
    vs
    vx
    vy
    cD
    cR
    cF
    cfili
    3adant1
    @3
    @9
    @13
    vs
    cF
    @3
    @7
    cF
    wcel
    #
    wa
    #
    @9
    @8
    vx
    @7
    wrex
    #
    @8
    vx
    cX
    wrex
    #
    @13
    @15
    @7
    c0
    wne
    #
    @9
    @16
    wi
    @3
    cF
    cX
    cfil
    cfv
    wcel
    #
    @14
    @18
    @0
    @1
    @19
    @2
    cD
    cF
    cX
    cfilfil
    3adant3
    #
    @7
    cF
    cX
    fileln0
    sylan
    @18
    @9
    @16
    @8
    vx
    @7
    r19.2z
    ex
    syl
    @15
    @7
    cX
    wss
    #
    @16
    @17
    wi
    @3
    @19
    @14
    @21
    @20
    @7
    cF
    cX
    filelss
    sylan
    #
    @8
    vx
    @7
    cX
    ssrexv
    syl
    @15
    @8
    @12
    vx
    cX
    @15
    @4
    cX
    wcel
    #
    wa
    #
    @8
    @7
    @11
    wss
    #
    @12
    @25
    @5
    @11
    wcel
    #
    vy
    @7
    wral
    @24
    @8
    vy
    @7
    @11
    dfss3
    @24
    @26
    @6
    vy
    @7
    @24
    @5
    @7
    wcel
    #
    wa
    @0
    cR
    cxr
    wcel
    #
    @23
    @5
    cX
    wcel
    @26
    @6
    wb
    @15
    @0
    @23
    @27
    @0
    @1
    @2
    @14
    simpl1
    #
    ad2antrr
    @24
    @28
    @27
    @24
    cR
    @0
    @1
    @2
    @14
    @23
    simpll3
    rpxrd
    #
    adantr
    @15
    @23
    @27
    simplr
    @24
    @7
    cX
    @5
    @15
    @21
    @23
    @22
    adantr
    sselda
    @5
    cD
    @4
    cR
    cX
    elbl2
    syl22anc
    ralbidva
    syl5bb
    @24
    @19
    @14
    @11
    cX
    wss
    #
    @25
    @12
    wi
    @3
    @19
    @14
    @23
    @20
    ad2antrr
    @3
    @14
    @23
    simplr
    @24
    @0
    @23
    @28
    @31
    @15
    @0
    @23
    @29
    adantr
    @15
    @23
    simpr
    @30
    cD
    @4
    cR
    cX
    blssm
    syl3anc
    @19
    @14
    @31
    @25
    @12
    @7
    @11
    cF
    cX
    filss
    3exp2
    syl3c
    sylbird
    reximdva
    3syld
    rexlimdva
    mpd
end
