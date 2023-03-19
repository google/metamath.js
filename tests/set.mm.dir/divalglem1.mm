include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "caddc.mm"
include "wo.mm"
include "zrei.mm"
include "0re.mm"
include "letrii.mm"
include "c1.mm"
include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wne.mm"
include "nnabscl.mm"
include "mp2an.mm"
include "nnge1.mm"
include "ax-mp.mm"
include "cr.mm"
include "wb.mm"
include "le0neg1.mm"
include "wa.mm"
include "renegcli.mm"
include "recni.mm"
include "abscli.mm"
include "lemulge11.mm"
include "mpanl12.mm"
include "sylanb.mm"
include "mpan2.mm"
include "absmuli.mm"
include "absnidi.mm"
include "oveq1d.mm"
include "syl5eq.mm"
include "breqtrrd.mm"
include "le0neg2.mm"
include "remulcli.mm"
include "absge0i.mm"
include "letri.mm"
include "sylbi.mm"
include "jaoi.mm"
include "cmin.mm"
include "df-neg.mm"
include "breq1i.mm"
include "lesubadd2i.mm"
include "bitri.mm"
include "mpbi.mm"

theorem divalglem1
  let cD: class D
  let cN: class N
  assume divalglem0.1: |- N e. ZZ
  assume divalglem0.2: |- D e. ZZ
  assume divalglem1.3: |- D =/= 0


  assert |- 0 <_ ( N + ( abs ` ( N x. D ) ) )

  proof
    cN
    cneg
    #
    cN
    cD
    cmul
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    cc0
    cN
    @2
    caddc
    co
    cle
    wbr
    #
    cN
    cc0
    cle
    wbr
    #
    cc0
    cN
    cle
    wbr
    #
    wo
    @3
    cN
    cc0
    cN
    divalglem0.1
    zrei
    #
    0re
    letrii
    @5
    @3
    @6
    @5
    @0
    @0
    cD
    cabs
    cfv
    #
    cmul
    co
    #
    @2
    cle
    @5
    c1
    @8
    cle
    wbr
    #
    @0
    @9
    cle
    wbr
    #
    @8
    cn
    wcel
    #
    @10
    cD
    cz
    wcel
    cD
    cc0
    wne
    @12
    divalglem0.2
    divalglem1.3
    cD
    nnabscl
    mp2an
    @8
    nnge1
    ax-mp
    @5
    cc0
    @0
    cle
    wbr
    #
    @10
    @11
    cN
    cr
    wcel
    #
    @5
    @13
    wb
    @7
    cN
    le0neg1
    ax-mp
    @0
    cr
    wcel
    @8
    cr
    wcel
    @13
    @10
    wa
    @11
    cN
    @7
    renegcli
    #
    cD
    cD
    cD
    divalglem0.2
    zrei
    #
    recni
    #
    abscli
    @0
    @8
    lemulge11
    mpanl12
    sylanb
    mpan2
    @5
    @2
    cN
    cabs
    cfv
    #
    @8
    cmul
    co
    @9
    cN
    cD
    cN
    @7
    recni
    @17
    absmuli
    @5
    @18
    @0
    @8
    cmul
    cN
    @7
    absnidi
    oveq1d
    syl5eq
    breqtrrd
    @6
    @0
    cc0
    cle
    wbr
    #
    @3
    @14
    @6
    @19
    wb
    @7
    cN
    le0neg2
    ax-mp
    @19
    cc0
    @2
    cle
    wbr
    @3
    @1
    @1
    cN
    cD
    @7
    @16
    remulcli
    recni
    #
    absge0i
    @0
    cc0
    @2
    @15
    0re
    @1
    @20
    abscli
    #
    letri
    mpan2
    sylbi
    jaoi
    ax-mp
    @3
    cc0
    cN
    cmin
    co
    #
    @2
    cle
    wbr
    @4
    @0
    @22
    @2
    cle
    cN
    df-neg
    breq1i
    cc0
    cN
    @2
    0re
    @7
    @21
    lesubadd2i
    bitri
    mpbi
end
