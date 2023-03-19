include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ccfil.mm"
include "cfil.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "wa.mm"
include "cfilfil.mm"
include "cfil3i.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "jca.mm"
include "clt.mm"
include "wbr.mm"
include "simprl.mm"
include "c2.mm"
include "cdiv.mm"
include "wi.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "simprr.mm"
include "cr.mm"
include "wss.mm"
include "simp-4l.mm"
include "simplrl.mm"
include "simpllr.mm"
include "rpred.mm"
include "blhalf.mm"
include "syl22anc.mm"
include "sseldd.mm"
include "cxr.mm"
include "wb.mm"
include "rpxrd.mm"
include "blssm.mm"
include "syl3anc.mm"
include "elbl2.mm"
include "mpbid.mm"
include "ralrimivva.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdvaa.mm"
include "syld.mm"
include "ralrimdva.mm"
include "impr.mm"
include "iscfil2.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "impbida.mm"

theorem iscfil3
  let vx: setvar x
  let cD: class D
  let cF: class F
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  let cG: class G
  let cJ: class J
  let cR: class R
  let cY: class Y
  let vd: setvar d

  disjoint r x
  disjoint F r
  disjoint F x
  disjoint X r
  disjoint X x
  disjoint D r
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
  disjoint r y
  disjoint r z
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint X f
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
  disjoint D s
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  assert |- ( D e. ( *Met ` X ) -> ( F e. ( CauFil ` D ) <-> ( F e. ( Fil ` X ) /\ A. r e. RR+ E. x e. X ( x ( ball ` D ) r ) e. F ) ) )

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
    cF
    cX
    cfil
    cfv
    wcel
    #
    vx
    cv
    #
    vr
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    cF
    wcel
    #
    vx
    cX
    wrex
    #
    vr
    crp
    wral
    #
    wa
    #
    @0
    @1
    wa
    #
    @2
    @9
    cD
    cF
    cX
    cfilfil
    @11
    @8
    vr
    crp
    @0
    @1
    @4
    crp
    wcel
    @8
    vx
    cD
    @4
    cF
    cX
    cfil3i
    3expa
    ralrimiva
    jca
    @0
    @10
    wa
    @1
    @2
    vu
    cv
    #
    vv
    cv
    #
    cD
    co
    vs
    cv
    #
    clt
    wbr
    #
    vv
    vy
    cv
    #
    wral
    #
    vu
    @16
    wral
    #
    vy
    cF
    wrex
    #
    vs
    crp
    wral
    #
    @0
    @2
    @9
    simprl
    @0
    @2
    @9
    @20
    @0
    @2
    wa
    #
    @9
    @19
    vs
    crp
    @21
    @14
    crp
    wcel
    #
    wa
    #
    @9
    @3
    @14
    c2
    cdiv
    co
    #
    @5
    co
    #
    cF
    wcel
    #
    vx
    cX
    wrex
    #
    @19
    @23
    @24
    crp
    wcel
    #
    @9
    @27
    wi
    @22
    @28
    @21
    @14
    rphalfcl
    #
    adantl
    @8
    @27
    vr
    @24
    crp
    @4
    @24
    wceq
    #
    @7
    @26
    vx
    cX
    @30
    @6
    @25
    cF
    @4
    @24
    @3
    @5
    oveq2
    eleq1d
    rexbidv
    rspcv
    syl
    @23
    @26
    @19
    vx
    cX
    @23
    @3
    cX
    wcel
    #
    @26
    wa
    #
    wa
    #
    @26
    @15
    vv
    @25
    wral
    #
    vu
    @25
    wral
    #
    @19
    @23
    @31
    @26
    simprr
    @33
    @15
    vu
    vv
    @25
    @25
    @33
    @12
    @25
    wcel
    #
    @13
    @25
    wcel
    #
    wa
    #
    wa
    #
    @13
    @12
    @14
    @5
    co
    #
    wcel
    #
    @15
    @39
    @25
    @40
    @13
    @39
    @0
    @31
    @14
    cr
    wcel
    @36
    @25
    @40
    wss
    @0
    @2
    @22
    @32
    @38
    simp-4l
    #
    @23
    @31
    @26
    @38
    simplrl
    #
    @39
    @14
    @21
    @22
    @32
    @38
    simpllr
    #
    rpred
    @33
    @36
    @37
    simprl
    #
    @14
    cD
    cX
    @3
    @12
    blhalf
    syl22anc
    @33
    @36
    @37
    simprr
    #
    sseldd
    @39
    @0
    @14
    cxr
    wcel
    @12
    cX
    wcel
    @13
    cX
    wcel
    @41
    @15
    wb
    @42
    @39
    @14
    @44
    rpxrd
    @39
    @25
    cX
    @12
    @39
    @0
    @31
    @24
    cxr
    wcel
    @25
    cX
    wss
    @42
    @43
    @39
    @24
    @39
    @22
    @28
    @44
    @29
    syl
    rpxrd
    cD
    @3
    @24
    cX
    blssm
    syl3anc
    #
    @45
    sseldd
    @39
    @25
    cX
    @13
    @47
    @46
    sseldd
    @13
    cD
    @12
    @14
    cX
    elbl2
    syl22anc
    mpbid
    ralrimivva
    @18
    @35
    vy
    @25
    cF
    @17
    @34
    vu
    @16
    @25
    @15
    vv
    @16
    @25
    raleq
    raleqbi1dv
    rspcev
    syl2anc
    rexlimdvaa
    syld
    ralrimdva
    impr
    @0
    @1
    @2
    @20
    wa
    wb
    @10
    vs
    vy
    vu
    vv
    cD
    cF
    cX
    iscfil2
    adantr
    mpbir2and
    impbida
end
