include "cc0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wcel.mm"
include "wn.mm"
include "zrei.mm"
include "0re.mm"
include "lttri2i.mm"
include "cle.mm"
include "cz.mm"
include "w3a.mm"
include "wb.mm"
include "0z.mm"
include "nnzi.mm"
include "elfzm11.mm"
include "mp2an.mm"
include "mpbi.mm"
include "simp3i.mm"
include "simp1i.mm"
include "nnrei.mm"
include "remulcli.mm"
include "ltadd1i.mm"
include "cneg.mm"
include "cr.mm"
include "renegcli.mm"
include "wa.mm"
include "nnnn0i.mm"
include "nn0ge0i.mm"
include "lemulge12.mm"
include "an4s.mm"
include "mpanl12.mm"
include "mpan.mm"
include "lt0neg1.mm"
include "ax-mp.mm"
include "znegcl.mm"
include "zltp1le.mm"
include "0p1e1.mm"
include "breq1i.mm"
include "bitri.mm"
include "recni.mm"
include "mulneg1i.mm"
include "oveq2i.mm"
include "subnegi.mm"
include "eqtri.mm"
include "suble0.mm"
include "bitr3i.mm"
include "3imtr4i.mm"
include "readdcli.mm"
include "ltletri.mm"
include "sylancr.mm"
include "ltnlei.mm"
include "sylib.mm"
include "elfzle1.mm"
include "nsyl.mm"
include "sylbi.mm"
include "simp2i.mm"
include "addge02.mm"
include "letri.mm"
include "sylancl.mm"
include "lenlti.mm"
include "simp3bi.mm"
include "jaoi.mm"

theorem divalglem6
  let cA: class A
  let cK: class K
  let cX: class X
  assume divalglem6.1: |- A e. NN
  assume divalglem6.2: |- X e. ( 0 ... ( A - 1 ) )
  assume divalglem6.3: |- K e. ZZ


  assert |- ( K =/= 0 -> -. ( X + ( K x. A ) ) e. ( 0 ... ( A - 1 ) ) )

  proof
    cK
    cc0
    wne
    cK
    cc0
    clt
    wbr
    #
    cc0
    cK
    clt
    wbr
    #
    wo
    cX
    cK
    cA
    cmul
    co
    #
    caddc
    co
    #
    cc0
    cA
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wn
    #
    cK
    cc0
    cK
    divalglem6.3
    zrei
    #
    0re
    lttri2i
    @0
    @7
    @1
    @0
    cc0
    @3
    cle
    wbr
    #
    @6
    @0
    @3
    cc0
    clt
    wbr
    #
    @9
    wn
    @0
    @3
    cA
    @2
    caddc
    co
    #
    clt
    wbr
    #
    @11
    cc0
    cle
    wbr
    #
    @10
    cX
    cA
    clt
    wbr
    #
    @12
    cX
    cz
    wcel
    #
    cc0
    cX
    cle
    wbr
    #
    @14
    cX
    @5
    wcel
    #
    @15
    @16
    @14
    w3a
    #
    divalglem6.2
    cc0
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    @17
    @18
    wb
    0z
    cA
    divalglem6.1
    nnzi
    #
    cX
    cc0
    cA
    elfzm11
    mp2an
    mpbi
    #
    simp3i
    cX
    cA
    @2
    cX
    @15
    @16
    @14
    @22
    simp1i
    zrei
    #
    cA
    divalglem6.1
    nnrei
    #
    cK
    cA
    @8
    @24
    remulcli
    #
    ltadd1i
    mpbi
    c1
    cK
    cneg
    #
    cle
    wbr
    #
    cA
    @26
    cA
    cmul
    co
    #
    cle
    wbr
    #
    @0
    @13
    @26
    cr
    wcel
    #
    @27
    @29
    cK
    @8
    renegcli
    #
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    @30
    @27
    wa
    @29
    @24
    cA
    cA
    divalglem6.1
    nnnn0i
    nn0ge0i
    #
    @32
    @30
    @33
    @27
    @29
    cA
    @26
    lemulge12
    an4s
    mpanl12
    mpan
    @0
    cc0
    @26
    clt
    wbr
    #
    @27
    cK
    cr
    wcel
    #
    @0
    @35
    wb
    @8
    cK
    lt0neg1
    ax-mp
    @35
    cc0
    c1
    caddc
    co
    #
    @26
    cle
    wbr
    #
    @27
    @19
    @26
    cz
    wcel
    #
    @35
    @38
    wb
    0z
    cK
    cz
    wcel
    #
    @39
    divalglem6.3
    cK
    znegcl
    ax-mp
    cc0
    @26
    zltp1le
    mp2an
    @37
    c1
    @26
    cle
    0p1e1
    breq1i
    bitri
    bitri
    @13
    cA
    @28
    cmin
    co
    #
    cc0
    cle
    wbr
    #
    @29
    @41
    @11
    cc0
    cle
    @41
    cA
    @2
    cneg
    #
    cmin
    co
    @11
    @28
    @43
    cA
    cmin
    cK
    cA
    cK
    @8
    recni
    cA
    @24
    recni
    #
    mulneg1i
    oveq2i
    cA
    @2
    @44
    @2
    @25
    recni
    subnegi
    eqtri
    breq1i
    @32
    @28
    cr
    wcel
    @42
    @29
    wb
    @24
    @26
    cA
    @31
    @24
    remulcli
    cA
    @28
    suble0
    mp2an
    bitr3i
    3imtr4i
    @3
    @11
    cc0
    cX
    @2
    @23
    @25
    readdcli
    #
    cA
    @2
    @24
    @25
    readdcli
    0re
    ltletri
    sylancr
    @3
    cc0
    @45
    0re
    ltnlei
    sylib
    @3
    cc0
    @4
    elfzle1
    nsyl
    @1
    @3
    cA
    clt
    wbr
    #
    @6
    @1
    cA
    @3
    cle
    wbr
    #
    @46
    wn
    @1
    cA
    @2
    cle
    wbr
    #
    @2
    @3
    cle
    wbr
    #
    @47
    @1
    c1
    cK
    cle
    wbr
    #
    @48
    @1
    @37
    cK
    cle
    wbr
    #
    @50
    @19
    @40
    @1
    @51
    wb
    0z
    divalglem6.3
    cc0
    cK
    zltp1le
    mp2an
    @37
    c1
    cK
    cle
    0p1e1
    breq1i
    bitri
    @33
    @50
    @48
    @34
    @32
    @36
    @33
    @50
    wa
    @48
    @24
    @8
    cA
    cK
    lemulge12
    mpanl12
    mpan
    sylbi
    @16
    @49
    @15
    @16
    @14
    @22
    simp2i
    @2
    cr
    wcel
    cX
    cr
    wcel
    @16
    @49
    wb
    @25
    @23
    @2
    cX
    addge02
    mp2an
    mpbi
    cA
    @2
    @3
    @24
    @25
    @45
    letri
    sylancl
    cA
    @3
    @24
    @45
    lenlti
    sylib
    @6
    @3
    cz
    wcel
    #
    @9
    @46
    @19
    @20
    @6
    @52
    @9
    @46
    w3a
    wb
    0z
    @21
    @3
    cc0
    cA
    elfzm11
    mp2an
    simp3bi
    nsyl
    jaoi
    sylbi
end
