include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cres.mm"
include "wf.mm"
include "cuz.mm"
include "crn.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "cbl.mm"
include "crp.mm"
include "cxmt.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "syl.mm"
include "lmbr.mm"
include "wb.mm"
include "wa.mm"
include "cxr.mm"
include "rpxr.mm"
include "blopn.mm"
include "syl3an3.mm"
include "blcntr.mm"
include "wceq.mm"
include "eleq2.mm"
include "feq3.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "impancom.mm"
include "syl2anc.mm"
include "3expa.mm"
include "adantlrl.mm"
include "ralrimiv.mm"
include "wss.mm"
include "mopni2.mm"
include "r19.29.mm"
include "fss.mm"
include "expcom.mm"
include "reximdv.mm"
include "impcom.mm"
include "rexlimivw.mm"
include "sylan2.mm"
include "3exp2.mm"
include "adantlr.mm"
include "impbida.mm"
include "pm5.32da.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem lmmbr
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cP: class P
  let cF: class F
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let cM: class M
  let cR: class R
  let cZ: class Z
  assume lmmbr.2: |- J = ( MetOpen ` D )
  assume lmmbr.3: |- ( ph -> D e. ( *Met ` X ) )

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint P x
  disjoint P y
  disjoint X x
  disjoint X y
  disjoint J x
  disjoint J y
  disjoint ph x
  disjoint j k
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint D j
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint D k
  disjoint u x
  disjoint u y
  disjoint D u
  disjoint F j
  disjoint F k
  disjoint F u
  disjoint P j
  disjoint P k
  disjoint P u
  disjoint X j
  disjoint X k
  disjoint X u
  disjoint J u
  disjoint M j
  disjoint j ph
  disjoint k ph
  disjoint ph u
  disjoint R j
  disjoint R k
  disjoint R x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> ( F e. ( X ^pm CC ) /\ P e. X /\ A. x e. RR+ E. y e. ran ZZ>= ( F |` y ) : y --> ( P ( ball ` D ) x ) ) ) )

  proof
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    cP
    cX
    wcel
    #
    cP
    vu
    cv
    #
    wcel
    #
    vy
    cv
    #
    @2
    cF
    @4
    cres
    #
    wf
    #
    vy
    cuz
    crn
    #
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    w3a
    #
    @0
    @1
    @4
    cP
    vx
    cv
    #
    cD
    cbl
    cfv
    co
    #
    @5
    wf
    #
    vy
    @7
    wrex
    #
    vx
    crp
    wral
    #
    w3a
    #
    wph
    vy
    vu
    cP
    cF
    cJ
    cX
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    lmmbr.3
    cD
    cJ
    cX
    lmmbr.2
    mopntopon
    syl
    lmbr
    wph
    @18
    @11
    @17
    wb
    lmmbr.3
    @18
    @0
    @1
    wa
    #
    @10
    wa
    @19
    @16
    wa
    @11
    @17
    @18
    @19
    @10
    @16
    @18
    @19
    wa
    #
    @10
    @16
    @20
    @10
    wa
    @15
    vx
    crp
    @20
    @12
    crp
    wcel
    #
    @10
    @15
    @18
    @1
    @21
    @10
    @15
    wi
    #
    @0
    @18
    @1
    @21
    @22
    @18
    @1
    @21
    w3a
    @13
    cJ
    wcel
    #
    cP
    @13
    wcel
    #
    @22
    @21
    @18
    @1
    @12
    cxr
    wcel
    @23
    @12
    rpxr
    cD
    cP
    @12
    cJ
    cX
    lmmbr.2
    blopn
    syl3an3
    cD
    cP
    @12
    cX
    blcntr
    @23
    @10
    @24
    @15
    @9
    @24
    @15
    wi
    vu
    @13
    cJ
    @2
    @13
    wceq
    #
    @3
    @24
    @8
    @15
    @2
    @13
    cP
    eleq2
    @25
    @6
    @14
    vy
    @7
    @2
    @13
    @4
    @5
    feq3
    rexbidv
    imbi12d
    rspcva
    impancom
    syl2anc
    3expa
    adantlrl
    impancom
    ralrimiv
    @20
    @16
    wa
    @9
    vu
    cJ
    @18
    @16
    @2
    cJ
    wcel
    #
    @9
    wi
    #
    @19
    @16
    @18
    @27
    @16
    @18
    @26
    @3
    @8
    @18
    @26
    @3
    w3a
    @16
    @13
    @2
    wss
    #
    vx
    crp
    wrex
    #
    @8
    vx
    @2
    cD
    cP
    cJ
    cX
    lmmbr.2
    mopni2
    @16
    @29
    wa
    @15
    @28
    wa
    #
    vx
    crp
    wrex
    @8
    @15
    @28
    vx
    crp
    r19.29
    @30
    @8
    vx
    crp
    @28
    @15
    @8
    @28
    @14
    @6
    vy
    @7
    @14
    @28
    @6
    @4
    @13
    @2
    @5
    fss
    expcom
    reximdv
    impcom
    rexlimivw
    syl
    sylan2
    3exp2
    impcom
    adantlr
    ralrimiv
    impbida
    pm5.32da
    @0
    @1
    @10
    df-3an
    @0
    @1
    @16
    df-3an
    3bitr4g
    syl
    bitrd
end
