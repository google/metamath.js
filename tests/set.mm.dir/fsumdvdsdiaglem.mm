include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "wcel.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "elrabi.mm"
include "ad2antll.mm"
include "breq1.mm"
include "elrab.mm"
include "simprbi.mm"
include "adantr.mm"
include "simprl.mm"
include "dvdsdivcl.mm"
include "syl2anc.mm"
include "syl.mm"
include "cz.mm"
include "wi.mm"
include "nnzd.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "sylanbrc.mm"
include "ad2antrl.mm"
include "cmul.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "nnne0d.mm"
include "dvdsmulcr.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "nncnd.mm"
include "divcan1d.mm"
include "divcan2d.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "ssrab2.mm"
include "sseldi.mm"
include "dvdscmulr.mm"
include "mpbid.mm"
include "jca.mm"
include "ex.mm"

theorem fsumdvdsdiaglem
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cN: class N
  assume fsumdvdsdiag.1: |- ( ph -> N e. NN )

  disjoint j k
  disjoint j x
  disjoint N j
  disjoint k x
  disjoint N k
  disjoint N x
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> ( ( j e. { x e. NN | x || N } /\ k e. { x e. NN | x || ( N / j ) } ) -> ( k e. { x e. NN | x || N } /\ j e. { x e. NN | x || ( N / k ) } ) ) )

  proof
    wph
    vj
    cv
    #
    vx
    cv
    #
    cN
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    wcel
    #
    vk
    cv
    #
    @1
    cN
    @0
    cdiv
    co
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    wcel
    #
    wa
    #
    @5
    @3
    wcel
    #
    @0
    @1
    cN
    @5
    cdiv
    co
    #
    cdvds
    wbr
    #
    vx
    cn
    crab
    wcel
    #
    wa
    wph
    @9
    wa
    #
    @10
    @13
    @14
    @5
    cn
    wcel
    #
    @5
    cN
    cdvds
    wbr
    #
    @10
    @8
    @15
    wph
    @4
    @7
    vx
    @5
    cn
    elrabi
    ad2antll
    #
    @14
    @5
    @6
    cdvds
    wbr
    #
    @6
    cN
    cdvds
    wbr
    #
    @16
    @8
    @18
    wph
    @4
    @8
    @15
    @18
    @7
    @18
    vx
    @5
    cn
    @1
    @5
    @6
    cdvds
    breq1
    elrab
    simprbi
    ad2antll
    #
    @14
    @6
    @3
    wcel
    #
    @19
    @14
    cN
    cn
    wcel
    #
    @4
    @21
    wph
    @22
    @9
    fsumdvdsdiag.1
    adantr
    #
    wph
    @4
    @8
    simprl
    vx
    @0
    cN
    dvdsdivcl
    syl2anc
    #
    @21
    @6
    cn
    wcel
    #
    @19
    @2
    @19
    vx
    @6
    cn
    @1
    @6
    cN
    cdvds
    breq1
    elrab
    simprbi
    syl
    @14
    @5
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    cN
    cz
    wcel
    @18
    @19
    wa
    @16
    wi
    @14
    @5
    @17
    nnzd
    #
    @14
    @6
    @14
    @21
    @25
    @24
    @2
    vx
    @6
    cn
    elrabi
    syl
    nnzd
    #
    @14
    cN
    @23
    nnzd
    @5
    @6
    cN
    dvdstr
    syl3anc
    mp2and
    @2
    @16
    vx
    @5
    cn
    @1
    @5
    cN
    cdvds
    breq1
    elrab
    sylanbrc
    #
    @14
    @0
    cn
    wcel
    #
    @0
    @11
    cdvds
    wbr
    #
    @13
    @4
    @31
    wph
    @8
    @2
    vx
    @0
    cn
    elrabi
    ad2antrl
    #
    @14
    @5
    @0
    cmul
    co
    #
    @5
    @11
    cmul
    co
    #
    cdvds
    wbr
    #
    @32
    @14
    @34
    @6
    @0
    cmul
    co
    #
    @35
    cdvds
    @14
    @34
    @37
    cdvds
    wbr
    #
    @18
    @20
    @14
    @26
    @27
    @0
    cz
    wcel
    #
    @0
    cc0
    wne
    @38
    @18
    wb
    @28
    @29
    @14
    @0
    @33
    nnzd
    #
    @14
    @0
    @33
    nnne0d
    #
    @0
    @5
    @6
    dvdsmulcr
    syl112anc
    mpbird
    @14
    @37
    cN
    @35
    @14
    cN
    @0
    @14
    cN
    @23
    nncnd
    #
    @14
    @0
    @33
    nncnd
    @41
    divcan1d
    @14
    cN
    @5
    @42
    @14
    @5
    @17
    nncnd
    @14
    @5
    @17
    nnne0d
    #
    divcan2d
    eqtr4d
    breqtrd
    @14
    @39
    @11
    cz
    wcel
    @26
    @5
    cc0
    wne
    @36
    @32
    wb
    @40
    @14
    @11
    @14
    @3
    cn
    @11
    @2
    vx
    cn
    ssrab2
    @14
    @22
    @10
    @11
    @3
    wcel
    @23
    @30
    vx
    @5
    cN
    dvdsdivcl
    syl2anc
    sseldi
    nnzd
    @28
    @43
    @5
    @0
    @11
    dvdscmulr
    syl112anc
    mpbid
    @12
    @32
    vx
    @0
    cn
    @1
    @0
    @11
    cdvds
    breq1
    elrab
    sylanbrc
    jca
    ex
end
