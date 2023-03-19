include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cca.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "cv.mm"
include "cuz.mm"
include "cbl.mm"
include "cres.mm"
include "wf.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "wa.mm"
include "cdm.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "iscau.mm"
include "wb.mm"
include "wfun.mm"
include "cxp.mm"
include "wss.mm"
include "cvv.mm"
include "elfvdm.mm"
include "cnex.mm"
include "elpmg.mm"
include "sylancl.mm"
include "simprbda.mm"
include "ffvresb.mm"
include "syl.mm"
include "rexbidv.mm"
include "adantr.mm"
include "wi.mm"
include "uzid.mm"
include "adantl.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcv.mm"
include "c0.mm"
include "wn.mm"
include "cxr.mm"
include "n0i.mm"
include "cpw.mm"
include "blf.mm"
include "fdm.mm"
include "ndmovg.mm"
include "ex.mm"
include "con1d.mm"
include "simpl.mm"
include "syl56.mm"
include "adantld.mm"
include "ad2antrr.mm"
include "syld.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "3anbi123d.mm"
include "simp2.mm"
include "syl6.mm"
include "rpxr.mm"
include "elbl.mm"
include "syl3an3.mm"
include "xmetsym.mm"
include "3expa.mm"
include "3adantl3.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "3com23.mm"
include "anbi2d.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "ralbidv.mm"
include "3expia.mm"
include "pm5.21ndd.mm"
include "rexbidva.mm"
include "adantlr.mm"
include "ralbidva.mm"

theorem iscau2
  let vx: setvar x
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cX: class X
  let vd: setvar d
  let vf: setvar f
  let vm: setvar m
  let wph: wff ph
  let cM: class M
  let cZ: class Z

  disjoint j k
  disjoint j x
  disjoint D j
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint d f
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d x
  disjoint D d
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f x
  disjoint D f
  disjoint j m
  disjoint k m
  disjoint m x
  disjoint D m
  disjoint F f
  disjoint F m
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint X d
  disjoint X f
  disjoint X m
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint Z x
  assert |- ( D e. ( *Met ` X ) -> ( F e. ( Cau ` D ) <-> ( F e. ( X ^pm CC ) /\ A. x e. RR+ E. j e. ZZ A. k e. ( ZZ>= ` j ) ( k e. dom F /\ ( F ` k ) e. X /\ ( ( F ` k ) D ( F ` j ) ) < x ) ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cF
    cD
    cca
    cfv
    wcel
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    vj
    cv
    #
    cuz
    cfv
    #
    @2
    cF
    cfv
    #
    vx
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    cF
    @3
    cres
    wf
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @1
    vk
    cv
    #
    cF
    cdm
    #
    wcel
    #
    @11
    cF
    cfv
    #
    cX
    wcel
    #
    @14
    @4
    cD
    co
    #
    @5
    clt
    wbr
    #
    w3a
    #
    vk
    @3
    wral
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wa
    vx
    cD
    vj
    cF
    cX
    iscau
    @0
    @1
    @10
    @21
    @0
    @1
    wa
    #
    @9
    @20
    vx
    crp
    @22
    @5
    crp
    wcel
    #
    wa
    @9
    @13
    @14
    @7
    wcel
    #
    wa
    #
    vk
    @3
    wral
    #
    vj
    cz
    wrex
    #
    @20
    @22
    @9
    @27
    wb
    @23
    @22
    @8
    @26
    vj
    cz
    @22
    cF
    wfun
    #
    @8
    @26
    wb
    @0
    @1
    @28
    cF
    cc
    cX
    cxp
    wss
    #
    @0
    cX
    cxmt
    cdm
    #
    wcel
    cc
    cvv
    wcel
    @1
    @28
    @29
    wa
    wb
    cD
    cX
    cxmt
    elfvdm
    cnex
    cX
    cc
    cF
    @30
    cvv
    elpmg
    sylancl
    simprbda
    vk
    @3
    @7
    cF
    ffvresb
    syl
    rexbidv
    adantr
    @0
    @23
    @27
    @20
    wb
    @1
    @0
    @23
    wa
    #
    @26
    @19
    vj
    cz
    @31
    @2
    cz
    wcel
    #
    wa
    #
    @4
    cX
    wcel
    #
    @26
    @19
    @33
    @26
    @2
    @12
    wcel
    #
    @4
    @7
    wcel
    #
    wa
    #
    @34
    @33
    @2
    @3
    wcel
    #
    @26
    @37
    wi
    @32
    @38
    @31
    @2
    uzid
    adantl
    #
    @25
    @37
    vk
    @2
    @3
    @11
    @2
    wceq
    #
    @13
    @35
    @24
    @36
    @11
    @2
    @12
    eleq1
    #
    @40
    @14
    @4
    @7
    @11
    @2
    cF
    fveq2
    #
    eleq1d
    anbi12d
    rspcv
    syl
    @0
    @37
    @34
    wi
    @23
    @32
    @0
    @36
    @34
    @35
    @36
    @7
    c0
    wceq
    #
    wn
    @0
    @34
    @5
    cxr
    wcel
    #
    wa
    #
    @34
    @7
    @4
    n0i
    @0
    @45
    @43
    @0
    @6
    cdm
    cX
    cxr
    cxp
    #
    wceq
    #
    @45
    wn
    #
    @43
    wi
    @0
    @46
    cX
    cpw
    #
    @6
    wf
    @47
    cD
    cX
    blf
    @46
    @49
    @6
    fdm
    syl
    @47
    @48
    @43
    @4
    @5
    cX
    cxr
    @6
    ndmovg
    ex
    syl
    con1d
    @34
    @44
    simpl
    syl56
    adantld
    ad2antrr
    syld
    @33
    @19
    @35
    @34
    @4
    @4
    cD
    co
    #
    @5
    clt
    wbr
    #
    w3a
    #
    @34
    @33
    @38
    @19
    @52
    wi
    @39
    @18
    @52
    vk
    @2
    @3
    @40
    @13
    @35
    @15
    @34
    @17
    @51
    @41
    @40
    @14
    @4
    cX
    @42
    eleq1d
    @40
    @16
    @50
    @5
    clt
    @40
    @14
    @4
    @4
    cD
    @42
    oveq1d
    breq1d
    3anbi123d
    rspcv
    syl
    @35
    @34
    @51
    simp2
    syl6
    @31
    @34
    @26
    @19
    wb
    #
    wi
    @32
    @0
    @23
    @34
    @53
    @0
    @23
    @34
    w3a
    #
    @25
    @18
    vk
    @3
    @54
    @25
    @13
    @15
    @17
    wa
    #
    wa
    @18
    @54
    @24
    @55
    @13
    @0
    @34
    @23
    @24
    @55
    wb
    @0
    @34
    @23
    w3a
    #
    @24
    @15
    @4
    @14
    cD
    co
    #
    @5
    clt
    wbr
    #
    wa
    #
    @55
    @23
    @0
    @34
    @44
    @24
    @59
    wb
    @5
    rpxr
    @14
    cD
    @4
    @5
    cX
    elbl
    syl3an3
    @56
    @15
    @58
    @17
    @56
    @15
    wa
    @57
    @16
    @5
    clt
    @0
    @34
    @15
    @57
    @16
    wceq
    #
    @23
    @0
    @34
    @15
    @60
    @4
    @14
    cD
    cX
    xmetsym
    3expa
    3adantl3
    breq1d
    pm5.32da
    bitrd
    3com23
    anbi2d
    @13
    @15
    @17
    3anass
    syl6bbr
    ralbidv
    3expia
    adantr
    pm5.21ndd
    rexbidva
    adantlr
    bitrd
    ralbidva
    pm5.32da
    bitrd
end
