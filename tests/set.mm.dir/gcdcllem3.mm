include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cn.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "cle.mm"
include "wi.mm"
include "c1.mm"
include "cv.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wrex.mm"
include "cpr.mm"
include "wss.mm"
include "prssi.mm"
include "adantr.mm"
include "wo.mm"
include "neorian.mm"
include "prid1g.mm"
include "neeq1.mm"
include "rspcev.mm"
include "sylan.mm"
include "adantlr.mm"
include "prid2g.mm"
include "adantll.mm"
include "jaodan.mm"
include "sylan2br.mm"
include "gcdcllem1.mm"
include "syl2anc.mm"
include "wb.mm"
include "gcdcllem2.mm"
include "raleq.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "syl.mm"
include "mpbird.mm"
include "suprzcl2.mm"
include "mp3an1.mm"
include "sseldi.mm"
include "a1i.mm"
include "simprd.mm"
include "1dvds.mm"
include "anim12i.mm"
include "1z.mm"
include "breq1.mm"
include "elrab2.mm"
include "mpbiran.mm"
include "sylibr.mm"
include "suprzub.mm"
include "syl3anc.mm"
include "elnnz1.mm"
include "sylanbrc.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "sylib.mm"
include "biimpri.mm"
include "3impb.mm"
include "3expia.mm"
include "mpan.mm"
include "syl2im.mm"
include "3jca.mm"

theorem gcdcllem3
  let vz: setvar z
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume gcdcllem2.1: |- S = { z e. ZZ | A. n e. { M , N } z || n }
  assume gcdcllem2.2: |- R = { z e. ZZ | ( z || M /\ z || N ) }

  disjoint K z
  disjoint n z
  disjoint M n
  disjoint M z
  disjoint N n
  disjoint N z
  disjoint x z
  disjoint K x
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint M x
  disjoint y z
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ -. ( M = 0 /\ N = 0 ) ) -> ( sup ( R , RR , < ) e. NN /\ ( sup ( R , RR , < ) || M /\ sup ( R , RR , < ) || N ) /\ ( ( K e. ZZ /\ K || M /\ K || N ) -> K <_ sup ( R , RR , < ) ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cc0
    wceq
    cN
    cc0
    wceq
    wa
    wn
    #
    wa
    #
    cR
    cr
    clt
    csup
    #
    cn
    wcel
    #
    @5
    cM
    cdvds
    wbr
    #
    @5
    cN
    cdvds
    wbr
    #
    wa
    #
    cK
    cz
    wcel
    #
    cK
    cM
    cdvds
    wbr
    #
    cK
    cN
    cdvds
    wbr
    #
    w3a
    #
    cK
    @5
    cle
    wbr
    #
    wi
    @4
    @5
    cz
    wcel
    #
    c1
    @5
    cle
    wbr
    #
    @6
    @4
    cR
    cz
    @5
    cR
    vz
    cv
    #
    cM
    cdvds
    wbr
    #
    @17
    cN
    cdvds
    wbr
    #
    wa
    #
    vz
    cz
    crab
    #
    cz
    gcdcllem2.2
    @20
    vz
    cz
    ssrab2
    eqsstri
    #
    @4
    cR
    c0
    wne
    #
    vy
    cv
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cR
    wral
    #
    vx
    cz
    wrex
    #
    wa
    #
    @5
    cR
    wcel
    #
    @4
    @28
    cS
    c0
    wne
    #
    @25
    vy
    cS
    wral
    #
    vx
    cz
    wrex
    #
    wa
    #
    @4
    cM
    cN
    cpr
    #
    cz
    wss
    #
    vn
    cv
    #
    cc0
    wne
    #
    vn
    @34
    wrex
    #
    @33
    @2
    @35
    @3
    cM
    cN
    cz
    prssi
    adantr
    @3
    @2
    cM
    cc0
    wne
    #
    cN
    cc0
    wne
    #
    wo
    @38
    cM
    cc0
    cN
    cc0
    neorian
    @2
    @39
    @38
    @40
    @0
    @39
    @38
    @1
    @0
    cM
    @34
    wcel
    @39
    @38
    cM
    cN
    cz
    prid1g
    @37
    @39
    vn
    cM
    @34
    @36
    cM
    cc0
    neeq1
    rspcev
    sylan
    adantlr
    @1
    @40
    @38
    @0
    @1
    cN
    @34
    wcel
    @40
    @38
    cM
    cN
    cz
    prid2g
    @37
    @40
    vn
    cN
    @34
    @36
    cN
    cc0
    neeq1
    rspcev
    sylan
    adantll
    jaodan
    sylan2br
    vx
    vy
    vz
    @34
    cS
    vn
    gcdcllem2.1
    gcdcllem1
    syl2anc
    @2
    @28
    @33
    wb
    #
    @3
    @2
    cR
    cS
    wceq
    #
    @41
    vz
    cR
    cS
    vn
    cM
    cN
    gcdcllem2.1
    gcdcllem2.2
    gcdcllem2
    @42
    @23
    @30
    @27
    @32
    cR
    cS
    c0
    neeq1
    @42
    @26
    @31
    vx
    cz
    @25
    vy
    cR
    cS
    raleq
    rexbidv
    anbi12d
    syl
    adantr
    mpbird
    #
    cR
    cz
    wss
    #
    @23
    @27
    @29
    @22
    vx
    vy
    cR
    suprzcl2
    mp3an1
    syl
    #
    sseldi
    @4
    @44
    @27
    c1
    cR
    wcel
    #
    @16
    @44
    @4
    @22
    a1i
    @4
    @23
    @27
    @43
    simprd
    #
    @2
    @46
    @3
    @2
    c1
    cM
    cdvds
    wbr
    #
    c1
    cN
    cdvds
    wbr
    #
    wa
    #
    @46
    @0
    @48
    @1
    @49
    cM
    1dvds
    cN
    1dvds
    anim12i
    @46
    c1
    cz
    wcel
    @50
    1z
    @20
    @50
    vz
    c1
    cz
    cR
    @17
    c1
    wceq
    @18
    @48
    @19
    @49
    @17
    c1
    cM
    cdvds
    breq1
    @17
    c1
    cN
    cdvds
    breq1
    anbi12d
    gcdcllem2.2
    elrab2
    mpbiran
    sylibr
    adantr
    vx
    vy
    cR
    c1
    suprzub
    syl3anc
    @5
    elnnz1
    sylanbrc
    @4
    @15
    @9
    @4
    @29
    @15
    @9
    wa
    @45
    @24
    cM
    cdvds
    wbr
    #
    @24
    cN
    cdvds
    wbr
    #
    wa
    #
    @9
    vx
    @5
    cz
    cR
    @24
    @5
    wceq
    @51
    @7
    @52
    @8
    @24
    @5
    cM
    cdvds
    breq1
    @24
    @5
    cN
    cdvds
    breq1
    anbi12d
    cR
    @21
    @53
    vx
    cz
    crab
    gcdcllem2.2
    @20
    @53
    vz
    vx
    cz
    @17
    @24
    wceq
    @18
    @51
    @19
    @52
    @17
    @24
    cM
    cdvds
    breq1
    @17
    @24
    cN
    cdvds
    breq1
    anbi12d
    cbvrabv
    eqtri
    elrab2
    sylib
    simprd
    @4
    @27
    @13
    cK
    cR
    wcel
    #
    @14
    @47
    @10
    @11
    @12
    @54
    @54
    @10
    @11
    @12
    wa
    #
    wa
    @20
    @55
    vz
    cK
    cz
    cR
    @17
    cK
    wceq
    @18
    @11
    @19
    @12
    @17
    cK
    cM
    cdvds
    breq1
    @17
    cK
    cN
    cdvds
    breq1
    anbi12d
    gcdcllem2.2
    elrab2
    biimpri
    3impb
    @44
    @27
    @54
    @14
    wi
    @22
    @44
    @27
    @54
    @14
    vx
    vy
    cR
    cK
    suprzub
    3expia
    mpan
    syl2im
    3jca
end
