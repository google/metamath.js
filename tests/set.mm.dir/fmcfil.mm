include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
include "wf.mm"
include "w3a.mm"
include "cfm.mm"
include "co.mm"
include "ccfil.mm"
include "cv.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cdm.mm"
include "wceq.mm"
include "elfvdm.mm"
include "fmval.mm"
include "syl3an1.mm"
include "eleq1d.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "fbasrn.mm"
include "syl3anc.mm"
include "fgcfil.mm"
include "syl2anc.mm"
include "cvv.mm"
include "imassrn.mm"
include "wss.mm"
include "frn.mm"
include "3ad2ant3.mm"
include "syl5ss.mm"
include "ssexd.mm"
include "ralrimivw.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "rexrnmpt.mm"
include "syl.mm"
include "wa.mm"
include "wfn.mm"
include "simpl3.mm"
include "ffn.mm"
include "fbelss.mm"
include "sylan.mm"
include "oveq1.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "ralima.mm"
include "oveq2.mm"
include "bitrd.mm"
include "rexbidva.mm"
include "3bitrd.mm"

theorem fmcfil
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cD: class D
  let cF: class F
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vf: setvar f
  let vr: setvar r
  let cG: class G
  let cJ: class J
  let cR: class R
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
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
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
  assert |- ( ( D e. ( *Met ` X ) /\ B e. ( fBas ` Y ) /\ F : Y --> X ) -> ( ( ( X FilMap F ) ` B ) e. ( CauFil ` D ) <-> A. x e. RR+ E. y e. B A. z e. y A. w e. y ( ( F ` z ) D ( F ` w ) ) < x ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cB
    cY
    cfbas
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cB
    cX
    cF
    cfm
    co
    cfv
    #
    cD
    ccfil
    cfv
    #
    wcel
    cX
    vy
    cB
    cF
    vy
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    cfg
    co
    #
    @5
    wcel
    #
    vu
    cv
    #
    vv
    cv
    #
    cD
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vv
    vs
    cv
    #
    wral
    #
    vu
    @17
    wral
    #
    vs
    @9
    wrex
    #
    vx
    crp
    wral
    #
    vz
    cv
    cF
    cfv
    #
    vw
    cv
    cF
    cfv
    #
    cD
    co
    #
    @15
    clt
    wbr
    #
    vw
    @6
    wral
    #
    vz
    @6
    wral
    #
    vy
    cB
    wrex
    #
    vx
    crp
    wral
    @3
    @4
    @10
    @5
    @0
    cX
    cxmt
    cdm
    #
    wcel
    #
    @1
    @2
    @4
    @10
    wceq
    cD
    cX
    cxmt
    elfvdm
    #
    vy
    @29
    cB
    cF
    cX
    cY
    fmval
    syl3an1
    eleq1d
    @3
    @0
    @9
    cX
    cfbas
    cfv
    wcel
    #
    @11
    @21
    wb
    @0
    @1
    @2
    simp1
    @3
    @1
    @2
    @30
    @32
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    @0
    @1
    @30
    @2
    @31
    3ad2ant1
    #
    vy
    cB
    @9
    cF
    @29
    cY
    cX
    @9
    eqid
    fbasrn
    syl3anc
    vx
    vs
    vu
    vv
    @9
    cD
    cX
    fgcfil
    syl2anc
    @3
    @20
    @28
    vx
    crp
    @3
    @20
    @16
    vv
    @7
    wral
    #
    vu
    @7
    wral
    #
    vy
    cB
    wrex
    #
    @28
    @3
    @7
    cvv
    wcel
    #
    vy
    cB
    wral
    @20
    @37
    wb
    @3
    @38
    vy
    cB
    @3
    @7
    cX
    @29
    @34
    @3
    @7
    cF
    crn
    #
    cX
    cF
    @6
    imassrn
    @2
    @0
    @39
    cX
    wss
    @1
    cY
    cX
    cF
    frn
    3ad2ant3
    syl5ss
    ssexd
    ralrimivw
    @19
    @36
    vy
    vs
    cB
    @7
    @8
    cvv
    @8
    eqid
    @18
    @35
    vu
    @17
    @7
    @16
    vv
    @17
    @7
    raleq
    raleqbi1dv
    rexrnmpt
    syl
    @3
    @36
    @27
    vy
    cB
    @3
    @6
    cB
    wcel
    #
    wa
    #
    @36
    @22
    @13
    cD
    co
    #
    @15
    clt
    wbr
    #
    vv
    @7
    wral
    #
    vz
    @6
    wral
    #
    @27
    @41
    cF
    cY
    wfn
    #
    @6
    cY
    wss
    #
    @36
    @45
    wb
    @41
    @2
    @46
    @0
    @1
    @2
    @40
    simpl3
    cY
    cX
    cF
    ffn
    syl
    #
    @3
    @1
    @40
    @47
    @33
    cY
    cB
    @6
    fbelss
    sylan
    #
    @35
    @44
    vu
    vz
    cY
    @6
    cF
    @12
    @22
    wceq
    #
    @16
    @43
    vv
    @7
    @50
    @14
    @42
    @15
    clt
    @12
    @22
    @13
    cD
    oveq1
    breq1d
    ralbidv
    ralima
    syl2anc
    @41
    @44
    @26
    vz
    @6
    @41
    @46
    @47
    @44
    @26
    wb
    @48
    @49
    @43
    @25
    vv
    vw
    cY
    @6
    cF
    @13
    @23
    wceq
    @42
    @24
    @15
    clt
    @13
    @23
    @22
    cD
    oveq2
    breq1d
    ralima
    syl2anc
    ralbidv
    bitrd
    rexbidva
    bitrd
    ralbidv
    3bitrd
end
