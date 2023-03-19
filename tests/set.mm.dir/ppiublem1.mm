include "c6.mm"
include "cle.mm"
include "wbr.mm"
include "cprime.mm"
include "wcel.mm"
include "c4.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "c5.mm"
include "cfz.mm"
include "c1.mm"
include "cpr.mm"
include "wi.mm"
include "caddc.mm"
include "simpli.mm"
include "df-6.mm"
include "3brtr3i.mm"
include "nn0rei.mm"
include "5re.mm"
include "1re.mm"
include "leadd1i.mm"
include "mpbir.mm"
include "6re.mm"
include "5lt6.mm"
include "ltleii.mm"
include "letri.mm"
include "mp2an.mm"
include "wceq.mm"
include "wo.mm"
include "cuz.mm"
include "cfv.mm"
include "wb.mm"
include "cz.mm"
include "nn0zi.mm"
include "5nn.mm"
include "nnzi.mm"
include "eluz2.mm"
include "mpbir3an.mm"
include "elfzp12.mm"
include "ax-mp.mm"
include "c2.mm"
include "cdvds.mm"
include "c3.mm"
include "w3o.mm"
include "prmz.mm"
include "adantr.mm"
include "cn.mm"
include "2nn.mm"
include "6nn.mm"
include "w3a.mm"
include "cmul.mm"
include "3z.mm"
include "2z.mm"
include "dvdsmul2.mm"
include "3t2e6.mm"
include "breqtri.mm"
include "dvdsmod.mm"
include "mpan2.mm"
include "mp3an12.mm"
include "syl.mm"
include "uzid.mm"
include "simpl.mm"
include "dvdsprm.mm"
include "sylancr.mm"
include "bitrd.mm"
include "simpr.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "clt.mm"
include "wn.mm"
include "2lt4.mm"
include "2re.mm"
include "4re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "pm2.21i.mm"
include "syl6.mm"
include "sylbid.mm"
include "imbi1d.mm"
include "syl5ibcom.mm"
include "com3r.mm"
include "3nn.mm"
include "dvdsmul1.mm"
include "df-3.mm"
include "peano2uz.mm"
include "eqeltri.mm"
include "3lt4.mm"
include "3re.mm"
include "eleq1a.mm"
include "a1d.mm"
include "3jaoi.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "simpri.mm"
include "syl5bir.mm"
include "jaod.mm"
include "syl5bi.mm"
include "pm3.2i.mm"

theorem ppiublem1
  let cP: class P
  let cM: class M
  let cN: class N
  assume ppiublem1.1: |- ( N <_ 6 /\ ( ( P e. Prime /\ 4 <_ P ) -> ( ( P mod 6 ) e. ( N ... 5 ) -> ( P mod 6 ) e. { 1 , 5 } ) ) )
  assume ppiublem1.2: |- M e. NN0
  assume ppiublem1.3: |- N = ( M + 1 )
  assume ppiublem1.4: |- ( 2 || M \/ 3 || M \/ M e. { 1 , 5 } )


  assert |- ( M <_ 6 /\ ( ( P e. Prime /\ 4 <_ P ) -> ( ( P mod 6 ) e. ( M ... 5 ) -> ( P mod 6 ) e. { 1 , 5 } ) ) )

  proof
    cM
    c6
    cle
    wbr
    #
    cP
    cprime
    wcel
    #
    c4
    cP
    cle
    wbr
    #
    wa
    #
    cP
    c6
    cmo
    co
    #
    cM
    c5
    cfz
    co
    wcel
    #
    @4
    c1
    c5
    cpr
    #
    wcel
    #
    wi
    wi
    cM
    c5
    cle
    wbr
    #
    c5
    c6
    cle
    wbr
    @0
    @8
    cM
    c1
    caddc
    co
    #
    c5
    c1
    caddc
    co
    #
    cle
    wbr
    cN
    c6
    @9
    @10
    cle
    cN
    c6
    cle
    wbr
    #
    @3
    @4
    cN
    c5
    cfz
    co
    #
    wcel
    #
    @7
    wi
    wi
    #
    ppiublem1.1
    simpli
    ppiublem1.3
    df-6
    3brtr3i
    cM
    c5
    c1
    cM
    ppiublem1.2
    nn0rei
    #
    5re
    1re
    leadd1i
    mpbir
    #
    c5
    c6
    5re
    6re
    5lt6
    ltleii
    cM
    c5
    c6
    @15
    5re
    6re
    letri
    mp2an
    @5
    @4
    cM
    wceq
    #
    @4
    @9
    c5
    cfz
    co
    #
    wcel
    #
    wo
    #
    @3
    @7
    c5
    cM
    cuz
    cfv
    wcel
    #
    @5
    @20
    wb
    @21
    cM
    cz
    wcel
    c5
    cz
    wcel
    @8
    cM
    ppiublem1.2
    nn0zi
    c5
    5nn
    nnzi
    @16
    cM
    c5
    eluz2
    mpbir3an
    @4
    cM
    c5
    elfzp12
    ax-mp
    @3
    @17
    @7
    @19
    c2
    cM
    cdvds
    wbr
    #
    c3
    cM
    cdvds
    wbr
    #
    cM
    @6
    wcel
    #
    w3o
    @3
    @17
    @7
    wi
    #
    wi
    #
    ppiublem1.4
    @22
    @26
    @23
    @24
    @3
    @17
    @22
    @7
    @3
    c2
    @4
    cdvds
    wbr
    #
    @7
    wi
    @17
    @22
    @7
    wi
    @3
    @27
    c2
    cP
    wceq
    #
    @7
    @3
    @27
    c2
    cP
    cdvds
    wbr
    #
    @28
    @3
    cP
    cz
    wcel
    #
    @27
    @29
    wb
    #
    @1
    @30
    @2
    cP
    prmz
    adantr
    #
    c2
    cn
    wcel
    #
    c6
    cn
    wcel
    #
    @30
    @31
    2nn
    6nn
    @33
    @34
    @30
    w3a
    c2
    c6
    cdvds
    wbr
    @31
    c2
    c3
    c2
    cmul
    co
    #
    c6
    cdvds
    c3
    cz
    wcel
    #
    c2
    cz
    wcel
    #
    c2
    @35
    cdvds
    wbr
    3z
    2z
    c3
    c2
    dvdsmul2
    mp2an
    3t2e6
    breqtri
    c2
    cP
    c6
    dvdsmod
    mpan2
    mp3an12
    syl
    @3
    c2
    c2
    cuz
    cfv
    #
    wcel
    #
    @1
    @29
    @28
    wb
    @37
    @39
    2z
    c2
    uzid
    ax-mp
    #
    @1
    @2
    simpl
    #
    cP
    c2
    dvdsprm
    sylancr
    bitrd
    @3
    @28
    c4
    c2
    cle
    wbr
    #
    @7
    @3
    @42
    @28
    @2
    @1
    @2
    simpr
    #
    c2
    cP
    c4
    cle
    breq2
    syl5ibrcom
    @42
    @7
    c2
    c4
    clt
    wbr
    @42
    wn
    2lt4
    c2
    c4
    2re
    4re
    ltnlei
    mpbi
    pm2.21i
    syl6
    sylbid
    @17
    @27
    @22
    @7
    @4
    cM
    c2
    cdvds
    breq2
    imbi1d
    syl5ibcom
    com3r
    @3
    @17
    @23
    @7
    @3
    c3
    @4
    cdvds
    wbr
    #
    @7
    wi
    @17
    @23
    @7
    wi
    @3
    @44
    c3
    cP
    wceq
    #
    @7
    @3
    @44
    c3
    cP
    cdvds
    wbr
    #
    @45
    @3
    @30
    @44
    @46
    wb
    #
    @32
    c3
    cn
    wcel
    #
    @34
    @30
    @47
    3nn
    6nn
    @48
    @34
    @30
    w3a
    c3
    c6
    cdvds
    wbr
    @47
    c3
    @35
    c6
    cdvds
    @36
    @37
    c3
    @35
    cdvds
    wbr
    3z
    2z
    c3
    c2
    dvdsmul1
    mp2an
    3t2e6
    breqtri
    c3
    cP
    c6
    dvdsmod
    mpan2
    mp3an12
    syl
    @3
    c3
    @38
    wcel
    @1
    @46
    @45
    wb
    c3
    c2
    c1
    caddc
    co
    #
    @38
    df-3
    @39
    @49
    @38
    wcel
    @40
    c2
    c2
    peano2uz
    ax-mp
    eqeltri
    @41
    cP
    c3
    dvdsprm
    sylancr
    bitrd
    @3
    @45
    c4
    c3
    cle
    wbr
    #
    @7
    @3
    @50
    @45
    @2
    @43
    c3
    cP
    c4
    cle
    breq2
    syl5ibrcom
    @50
    @7
    c3
    c4
    clt
    wbr
    @50
    wn
    3lt4
    c3
    c4
    3re
    4re
    ltnlei
    mpbi
    pm2.21i
    syl6
    sylbid
    @17
    @44
    @23
    @7
    @4
    cM
    c3
    cdvds
    breq2
    imbi1d
    syl5ibcom
    com3r
    @24
    @25
    @3
    cM
    @6
    @4
    eleq1a
    a1d
    3jaoi
    ax-mp
    @19
    @13
    @3
    @7
    @12
    @18
    @4
    cN
    @9
    c5
    cfz
    ppiublem1.3
    oveq1i
    eleq2i
    @11
    @14
    ppiublem1.1
    simpri
    syl5bir
    jaod
    syl5bi
    pm3.2i
end
