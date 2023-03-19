include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ccfil.mm"
include "cfil.mm"
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
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "iscfil.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "cxr.mm"
include "wf.mm"
include "xmetf.mm"
include "ad3antrrr.mm"
include "ffun.mm"
include "syl.mm"
include "simplr.mm"
include "filelss.mm"
include "sylan.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "wceq.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimassov.mm"
include "cle.mm"
include "0xr.mm"
include "a1i.mm"
include "simpllr.mm"
include "rpxrd.mm"
include "simp-4l.mm"
include "sselda.mm"
include "adantrr.mm"
include "adantrl.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "xmetge0.mm"
include "w3a.mm"
include "elico1.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "baibd.mm"
include "syl22anc.mm"
include "2ralbidva.mm"
include "bitrd.mm"
include "rexbidva.mm"
include "ralbidva.mm"
include "pm5.32da.mm"

theorem iscfil2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cD: class D
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  let vf: setvar f
  let vr: setvar r
  let cG: class G
  let cJ: class J
  let cR: class R
  let cY: class Y
  let vd: setvar d

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
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
  assert |- ( D e. ( *Met ` X ) -> ( F e. ( CauFil ` D ) <-> ( F e. ( Fil ` X ) /\ A. x e. RR+ E. y e. F A. z e. y A. w e. y ( z D w ) < x ) ) )

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
    cF
    cX
    cfil
    cfv
    wcel
    #
    cD
    vy
    cv
    #
    @2
    cxp
    #
    cima
    cc0
    vx
    cv
    #
    cico
    co
    #
    wss
    #
    vy
    cF
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @1
    vz
    cv
    #
    vw
    cv
    #
    cD
    co
    #
    @4
    clt
    wbr
    #
    vw
    @2
    wral
    vz
    @2
    wral
    #
    vy
    cF
    wrex
    #
    vx
    crp
    wral
    #
    wa
    vx
    vy
    cD
    cF
    cX
    iscfil
    @0
    @1
    @8
    @15
    @0
    @1
    wa
    #
    @7
    @14
    vx
    crp
    @16
    @4
    crp
    wcel
    #
    wa
    #
    @6
    @13
    vy
    cF
    @18
    @2
    cF
    wcel
    #
    wa
    #
    @6
    @11
    @5
    wcel
    #
    vw
    @2
    wral
    vz
    @2
    wral
    #
    @13
    @20
    cD
    wfun
    #
    @3
    cD
    cdm
    #
    wss
    @6
    @22
    wb
    @20
    cX
    cX
    cxp
    #
    cxr
    cD
    wf
    #
    @23
    @0
    @26
    @1
    @17
    @19
    cD
    cX
    xmetf
    ad3antrrr
    #
    @25
    cxr
    cD
    ffun
    syl
    @20
    @3
    @25
    @24
    @20
    @2
    cX
    wss
    #
    @28
    @3
    @25
    wss
    @18
    @1
    @19
    @28
    @0
    @1
    @17
    simplr
    @2
    cF
    cX
    filelss
    sylan
    #
    @29
    @2
    cX
    @2
    cX
    xpss12
    syl2anc
    @20
    @26
    @24
    @25
    wceq
    @27
    @25
    cxr
    cD
    fdm
    syl
    sseqtr4d
    vz
    vw
    @2
    @2
    @5
    cD
    funimassov
    syl2anc
    @20
    @21
    @12
    vz
    vw
    @2
    @2
    @20
    @9
    @2
    wcel
    #
    @10
    @2
    wcel
    #
    wa
    #
    wa
    #
    cc0
    cxr
    wcel
    #
    @4
    cxr
    wcel
    #
    @11
    cxr
    wcel
    #
    cc0
    @11
    cle
    wbr
    #
    @21
    @12
    wb
    @34
    @33
    0xr
    a1i
    @33
    @4
    @16
    @17
    @19
    @32
    simpllr
    rpxrd
    @33
    @0
    @9
    cX
    wcel
    #
    @10
    cX
    wcel
    #
    @36
    @0
    @1
    @17
    @19
    @32
    simp-4l
    #
    @20
    @30
    @38
    @31
    @20
    @2
    cX
    @9
    @29
    sselda
    adantrr
    #
    @20
    @31
    @39
    @30
    @20
    @2
    cX
    @10
    @29
    sselda
    adantrl
    #
    @9
    @10
    cD
    cX
    xmetcl
    syl3anc
    @33
    @0
    @38
    @39
    @37
    @40
    @41
    @42
    @9
    @10
    cD
    cX
    xmetge0
    syl3anc
    @34
    @35
    wa
    #
    @21
    @36
    @37
    wa
    #
    @12
    @43
    @21
    @36
    @37
    @12
    w3a
    @44
    @12
    wa
    cc0
    @4
    @11
    elico1
    @36
    @37
    @12
    df-3an
    syl6bb
    baibd
    syl22anc
    2ralbidva
    bitrd
    rexbidva
    ralbidva
    pm5.32da
    bitrd
end
