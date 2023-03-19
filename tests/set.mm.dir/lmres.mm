include "cuz.mm"
include "cfv.mm"
include "cres.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "w3a.mm"
include "clm.mm"
include "wbr.mm"
include "cvv.mm"
include "wss.mm"
include "ctopon.mm"
include "toponmax.mm"
include "syl.mm"
include "cnex.mm"
include "ssid.mm"
include "cz.mm"
include "uzssz.mm"
include "zsscn.mm"
include "sstri.mm"
include "pmss12g.mm"
include "mpanl12.mm"
include "sylancl.mm"
include "fvex.mm"
include "pmresg.mm"
include "sylancr.mm"
include "sseldd.mm"
include "2thd.mm"
include "wb.mm"
include "eqid.mm"
include "uztrn2.mm"
include "dmres.mm"
include "elin2.mm"
include "baib.mm"
include "fvres.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "ralbidva.mm"
include "rexbiia.mm"
include "imbi2i.mm"
include "ralbii.mm"
include "a1i.mm"
include "3anbi13d.mm"
include "lmbr2.mm"
include "3bitr4rd.mm"

theorem lmres
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  assume lmres.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume lmres.4: |- ( ph -> F e. ( X ^pm CC ) )
  assume lmres.5: |- ( ph -> M e. ZZ )


  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> ( F |` ( ZZ>= ` M ) ) ( ~~>t ` J ) P ) )

  proof
    wph
    cF
    cM
    cuz
    cfv
    #
    cres
    #
    cX
    cc
    cpm
    co
    #
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
    vk
    cv
    #
    @1
    cdm
    #
    wcel
    #
    @7
    @1
    cfv
    #
    @5
    wcel
    #
    wa
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    @0
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    w3a
    cF
    @2
    wcel
    #
    @4
    @6
    @7
    cF
    cdm
    #
    wcel
    #
    @7
    cF
    cfv
    #
    @5
    wcel
    #
    wa
    #
    vk
    @14
    wral
    #
    vj
    @0
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    w3a
    @1
    cP
    cJ
    clm
    cfv
    #
    wbr
    cF
    cP
    @29
    wbr
    wph
    @3
    @19
    @18
    @28
    @4
    wph
    @3
    @19
    wph
    cX
    @0
    cpm
    co
    #
    @2
    @1
    wph
    cX
    cJ
    wcel
    #
    cc
    cvv
    wcel
    #
    @30
    @2
    wss
    #
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    @31
    lmres.2
    cX
    cJ
    toponmax
    syl
    cnex
    cX
    cX
    wss
    @0
    cc
    wss
    @31
    @32
    wa
    @33
    cX
    ssid
    @0
    cz
    cc
    cM
    uzssz
    zsscn
    sstri
    cX
    @0
    cX
    cc
    cJ
    cvv
    pmss12g
    mpanl12
    sylancl
    wph
    @0
    cvv
    wcel
    @19
    @1
    @30
    wcel
    cM
    cuz
    fvex
    lmres.4
    cX
    @0
    cc
    cF
    cvv
    pmresg
    sylancr
    sseldd
    lmres.4
    2thd
    @18
    @28
    wb
    wph
    @17
    @27
    vu
    cJ
    @16
    @26
    @6
    @15
    @25
    vj
    @0
    @13
    @0
    wcel
    #
    @12
    @24
    vk
    @14
    @34
    @7
    @14
    wcel
    wa
    @7
    @0
    wcel
    #
    @12
    @24
    wb
    cM
    @7
    @13
    @0
    @0
    eqid
    #
    uztrn2
    @35
    @9
    @21
    @11
    @23
    @9
    @35
    @21
    @7
    @0
    @20
    @8
    cF
    @0
    dmres
    elin2
    baib
    @35
    @10
    @22
    @5
    @7
    @0
    cF
    fvres
    eleq1d
    anbi12d
    syl
    ralbidva
    rexbiia
    imbi2i
    ralbii
    a1i
    3anbi13d
    wph
    vu
    cP
    vj
    vk
    @1
    cJ
    cM
    cX
    @0
    lmres.2
    @36
    lmres.5
    lmbr2
    wph
    vu
    cP
    vj
    vk
    cF
    cJ
    cM
    cX
    @0
    lmres.2
    @36
    lmres.5
    lmbr2
    3bitr4rd
end
