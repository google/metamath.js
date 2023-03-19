include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "c8.mm"
include "cmo.mm"
include "cc0.mm"
include "cfz.mm"
include "wi.mm"
include "simp1i.mm"
include "peano2z.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "simp2i.mm"
include "wb.mm"
include "2z.mm"
include "dvdsadd.mm"
include "mp2an.mm"
include "mpbi.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "addcomi.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "df-2.mm"
include "add32i.mm"
include "eqtr4i.mm"
include "2cn.mm"
include "addassi.mm"
include "breqtrri.mm"
include "cmin.mm"
include "wceq.mm"
include "wo.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuz2.mm"
include "fzm1.mm"
include "syl.mm"
include "ibi.mm"
include "subaddrii.mm"
include "oveq2i.mm"
include "eleq2s.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "simp3i.mm"
include "syl5bi.mm"
include "cn.mm"
include "2nn.mm"
include "8nn.mm"
include "w3a.mm"
include "c4.mm"
include "cmul.mm"
include "4z.mm"
include "dvdsmul2.mm"
include "4t2e8.mm"
include "breqtri.mm"
include "dvdsmod.mm"
include "mpan2.mm"
include "mp3an12.mm"
include "notbid.mm"
include "biimpar.mm"
include "id.mm"
include "syl5breqr.mm"
include "nsyl.mm"
include "pm2.21d.mm"
include "jaod.mm"
include "syl5.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "a1i.mm"
include "3pm3.2i.mm"

theorem lgsdir2lem2
  let cA: class A
  let cS: class S
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let cP: class P
  let wph: wff ph
  let vp: setvar p
  assume lgsdir2lem2.1: |- ( K e. ZZ /\ 2 || ( K + 1 ) /\ ( ( A e. ZZ /\ -. 2 || A ) -> ( ( A mod 8 ) e. ( 0 ... K ) -> ( A mod 8 ) e. S ) ) )
  assume lgsdir2lem2.2: |- M = ( K + 1 )
  assume lgsdir2lem2.3: |- N = ( M + 1 )
  assume lgsdir2lem2.4: |- N e. S


  assert |- ( N e. ZZ /\ 2 || ( N + 1 ) /\ ( ( A e. ZZ /\ -. 2 || A ) -> ( ( A mod 8 ) e. ( 0 ... N ) -> ( A mod 8 ) e. S ) ) )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    c1
    caddc
    co
    #
    cdvds
    wbr
    cA
    cz
    wcel
    #
    c2
    cA
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    cA
    c8
    cmo
    co
    #
    cc0
    cN
    cfz
    co
    wcel
    #
    @6
    cS
    wcel
    #
    wi
    wi
    cN
    cM
    c1
    caddc
    co
    #
    cz
    lgsdir2lem2.3
    cM
    cz
    wcel
    #
    @9
    cz
    wcel
    cM
    cK
    c1
    caddc
    co
    #
    cz
    lgsdir2lem2.2
    cK
    cz
    wcel
    #
    @11
    cz
    wcel
    #
    @12
    c2
    @11
    cdvds
    wbr
    #
    @5
    @6
    cc0
    cK
    cfz
    co
    #
    wcel
    #
    @8
    wi
    wi
    #
    lgsdir2lem2.1
    simp1i
    #
    cK
    peano2z
    ax-mp
    #
    eqeltri
    #
    cM
    peano2z
    ax-mp
    eqeltri
    #
    c2
    c2
    @11
    caddc
    co
    #
    @1
    cdvds
    @14
    c2
    @22
    cdvds
    wbr
    #
    @12
    @14
    @17
    lgsdir2lem2.1
    simp2i
    #
    c2
    cz
    wcel
    #
    @13
    @14
    @23
    wb
    2z
    @19
    c2
    @11
    dvdsadd
    mp2an
    mpbi
    @1
    c2
    cK
    caddc
    co
    #
    c1
    caddc
    co
    @22
    cN
    @26
    c1
    caddc
    cN
    c1
    cK
    caddc
    co
    #
    c1
    caddc
    co
    #
    @26
    cN
    @9
    @28
    lgsdir2lem2.3
    cM
    @27
    c1
    caddc
    cM
    @11
    @27
    lgsdir2lem2.2
    cK
    c1
    @12
    cK
    cc
    wcel
    @18
    cK
    zcn
    ax-mp
    #
    ax-1cn
    addcomi
    eqtri
    #
    oveq1i
    eqtri
    @26
    c1
    c1
    caddc
    co
    #
    cK
    caddc
    co
    @28
    c2
    @31
    cK
    caddc
    df-2
    oveq1i
    c1
    cK
    c1
    ax-1cn
    @29
    ax-1cn
    add32i
    eqtr4i
    eqtr4i
    oveq1i
    c2
    cK
    c1
    2cn
    @29
    ax-1cn
    addassi
    eqtri
    breqtrri
    @7
    @6
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    @6
    cN
    wceq
    #
    wo
    #
    @5
    @8
    @7
    @36
    @7
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @7
    @36
    wb
    @6
    cc0
    cN
    elfzuz2
    @6
    cc0
    cN
    fzm1
    syl
    ibi
    @5
    @34
    @8
    @35
    @34
    @6
    cc0
    cM
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    @6
    cM
    wceq
    #
    wo
    #
    @5
    @8
    @42
    @6
    cc0
    cM
    cfz
    co
    #
    @33
    @6
    @43
    wcel
    #
    @42
    @44
    cM
    @37
    wcel
    @44
    @42
    wb
    @6
    cc0
    cM
    elfzuz2
    @6
    cc0
    cM
    fzm1
    syl
    ibi
    @32
    cM
    cc0
    cfz
    cN
    c1
    cM
    @0
    cN
    cc
    wcel
    @21
    cN
    zcn
    ax-mp
    ax-1cn
    @10
    cM
    cc
    wcel
    @20
    cM
    zcn
    ax-mp
    #
    c1
    cM
    caddc
    co
    @9
    cN
    c1
    cM
    ax-1cn
    @45
    addcomi
    lgsdir2lem2.3
    eqtr4i
    subaddrii
    oveq2i
    eleq2s
    @5
    @40
    @8
    @41
    @40
    @16
    @5
    @8
    @39
    @15
    @6
    @38
    cK
    cc0
    cfz
    cM
    c1
    cK
    @45
    ax-1cn
    @29
    cM
    @27
    @30
    eqcomi
    subaddrii
    oveq2i
    eleq2i
    @12
    @14
    @17
    lgsdir2lem2.1
    simp3i
    syl5bi
    @5
    @41
    @8
    @5
    c2
    @6
    cdvds
    wbr
    #
    @41
    @2
    @46
    wn
    @4
    @2
    @46
    @3
    c2
    cn
    wcel
    #
    c8
    cn
    wcel
    #
    @2
    @46
    @3
    wb
    #
    2nn
    8nn
    @47
    @48
    @2
    w3a
    c2
    c8
    cdvds
    wbr
    @49
    c2
    c4
    c2
    cmul
    co
    #
    c8
    cdvds
    c4
    cz
    wcel
    @25
    c2
    @50
    cdvds
    wbr
    4z
    2z
    c4
    c2
    dvdsmul2
    mp2an
    4t2e8
    breqtri
    c2
    cA
    c8
    dvdsmod
    mpan2
    mp3an12
    notbid
    biimpar
    @41
    c2
    cM
    @6
    cdvds
    c2
    @11
    cM
    cdvds
    @24
    lgsdir2lem2.2
    breqtrri
    @41
    id
    syl5breqr
    nsyl
    pm2.21d
    jaod
    syl5
    @35
    @8
    wi
    @5
    @35
    @8
    cN
    cS
    wcel
    lgsdir2lem2.4
    @6
    cN
    cS
    eleq1
    mpbiri
    a1i
    jaod
    syl5
    3pm3.2i
end
