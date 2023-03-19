include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "cres.mm"
include "cca.mm"
include "uztrn2.mm"
include "adantll.mm"
include "biantrurd.mm"
include "dmres.mm"
include "elin2.mm"
include "syl6bbr.mm"
include "3anbi1d.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "cme.mm"
include "cvv.mm"
include "wss.mm"
include "elfvdm.mm"
include "syl.mm"
include "cnex.mm"
include "ssid.mm"
include "cz.mm"
include "uzssz.mm"
include "zsscn.mm"
include "sstri.mm"
include "eqsstri.mm"
include "pmss12g.mm"
include "mpanl12.mm"
include "sylancl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pmresg.mm"
include "sylancr.mm"
include "sseldd.mm"
include "3bitr3d.mm"
include "cxmt.mm"
include "metxmet.mm"
include "eqidd.mm"
include "iscau4.mm"
include "wceq.mm"
include "fvres.mm"
include "adantl.mm"
include "3bitr4d.mm"

theorem caures
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cG: class G
  let cN: class N
  let cW: class W
  assume caures.1: |- Z = ( ZZ>= ` M )
  assume caures.3: |- ( ph -> M e. ZZ )
  assume caures.4: |- ( ph -> D e. ( Met ` X ) )
  assume caures.5: |- ( ph -> F e. ( X ^pm CC ) )


  assert |- ( ph -> ( F e. ( Cau ` D ) <-> ( F |` Z ) e. ( Cau ` D ) ) )

  proof
    wph
    cF
    cX
    cc
    cpm
    co
    #
    wcel
    #
    vk
    cv
    #
    cF
    cdm
    #
    wcel
    #
    @2
    cF
    cfv
    #
    cX
    wcel
    #
    @5
    vj
    cv
    #
    cF
    cfv
    #
    cD
    co
    vx
    cv
    clt
    wbr
    #
    w3a
    #
    vk
    @7
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    cF
    cZ
    cres
    #
    @0
    wcel
    #
    @2
    @16
    cdm
    #
    wcel
    #
    @6
    @9
    w3a
    #
    vk
    @11
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    cF
    cD
    cca
    cfv
    #
    wcel
    @16
    @25
    wcel
    wph
    @14
    @23
    @15
    @24
    wph
    @13
    @22
    vx
    crp
    wph
    @12
    @21
    vj
    cZ
    wph
    @7
    cZ
    wcel
    #
    wa
    #
    @10
    @20
    vk
    @11
    @27
    @2
    @11
    wcel
    #
    wa
    #
    @4
    @19
    @6
    @9
    @29
    @4
    @2
    cZ
    wcel
    #
    @4
    wa
    @19
    @29
    @30
    @4
    @26
    @28
    @30
    wph
    cM
    @2
    @7
    cZ
    caures.1
    uztrn2
    adantll
    biantrurd
    @2
    cZ
    @3
    @18
    cF
    cZ
    dmres
    elin2
    syl6bbr
    3anbi1d
    ralbidva
    rexbidva
    ralbidv
    wph
    @1
    @14
    caures.5
    biantrurd
    wph
    @17
    @23
    wph
    cX
    cZ
    cpm
    co
    #
    @0
    @16
    wph
    cX
    cme
    cdm
    #
    wcel
    #
    cc
    cvv
    wcel
    #
    @31
    @0
    wss
    #
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    @33
    caures.4
    cD
    cX
    cme
    elfvdm
    syl
    cnex
    cX
    cX
    wss
    cZ
    cc
    wss
    @33
    @34
    wa
    @35
    cX
    ssid
    cZ
    cM
    cuz
    cfv
    #
    cc
    caures.1
    @37
    cz
    cc
    cM
    uzssz
    zsscn
    sstri
    eqsstri
    cX
    cZ
    cX
    cc
    @32
    cvv
    pmss12g
    mpanl12
    sylancl
    wph
    cZ
    cvv
    wcel
    @1
    @16
    @31
    wcel
    cZ
    @37
    cvv
    caures.1
    cM
    cuz
    fvex
    eqeltri
    caures.5
    cX
    cZ
    cc
    cF
    cvv
    pmresg
    sylancr
    sseldd
    biantrurd
    3bitr3d
    wph
    vx
    @5
    @8
    cD
    vj
    vk
    cF
    cM
    cX
    cZ
    caures.1
    wph
    @36
    cD
    cX
    cxmt
    cfv
    wcel
    caures.4
    cD
    cX
    metxmet
    syl
    #
    caures.3
    wph
    @30
    wa
    @5
    eqidd
    @27
    @8
    eqidd
    iscau4
    wph
    vx
    @5
    @8
    cD
    vj
    vk
    @16
    cM
    cX
    cZ
    caures.1
    @38
    caures.3
    @30
    @2
    @16
    cfv
    @5
    wceq
    wph
    @2
    cZ
    cF
    fvres
    adantl
    @26
    @7
    @16
    cfv
    @8
    wceq
    wph
    @7
    cZ
    cF
    fvres
    adantl
    iscau4
    3bitr4d
end
