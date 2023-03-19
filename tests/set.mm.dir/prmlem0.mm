include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "eldifi.mm"
include "eleq1.mm"
include "breq1.mm"
include "notbid.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "syl5.mm"
include "adantrd.mm"
include "a1i.mm"
include "wo.mm"
include "uzp1.mm"
include "wb.mm"
include "adantl.mm"
include "wne.mm"
include "eldifsn.mm"
include "cz.mm"
include "eluzel2.mm"
include "simpl.mm"
include "1z.mm"
include "n2dvds1.mm"
include "opoe.mm"
include "mpanr12.mm"
include "syl2anc.mm"
include "adantr.mm"
include "2z.mm"
include "uzid.mm"
include "mp1i.mm"
include "dvdsprm.mm"
include "sylan.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "a1d.mm"
include "necon3ad.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "ex.mm"
include "cc.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "addass.mm"
include "mp3an23.mm"
include "syl.mm"
include "1p1e2.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "dvdsaddr.mm"
include "sylancr.mm"
include "breq2i.mm"
include "syl6bb.mm"
include "mtbid.mm"
include "jaod.mm"
include "mpjaod.mm"

theorem prmlem0
  let vx: setvar x
  let cK: class K
  let cM: class M
  let cN: class N
  assume prmlem0.1: |- ( ( -. 2 || M /\ x e. ( ZZ>= ` M ) ) -> ( ( x e. ( Prime \ { 2 } ) /\ ( x ^ 2 ) <_ N ) -> -. x || N ) )
  assume prmlem0.2: |- ( K e. Prime -> -. K || N )
  assume prmlem0.3: |- ( K + 2 ) = M

  disjoint N x
  assert |- ( ( -. 2 || K /\ x e. ( ZZ>= ` K ) ) -> ( ( x e. ( Prime \ { 2 } ) /\ ( x ^ 2 ) <_ N ) -> -. x || N ) )

  proof
    c2
    cK
    cdvds
    wbr
    #
    wn
    #
    vx
    cv
    #
    cK
    cuz
    cfv
    wcel
    #
    wa
    #
    @2
    cK
    wceq
    #
    @2
    cprime
    c2
    csn
    #
    cdif
    #
    wcel
    #
    @2
    c2
    cexp
    co
    cN
    cle
    wbr
    #
    wa
    @2
    cN
    cdvds
    wbr
    #
    wn
    #
    wi
    #
    @2
    cK
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    @5
    @12
    wi
    @4
    @5
    @8
    @11
    @9
    @8
    @2
    cprime
    wcel
    #
    @5
    @11
    @2
    cprime
    @6
    eldifi
    @5
    @15
    @11
    wi
    cK
    cprime
    wcel
    #
    cK
    cN
    cdvds
    wbr
    #
    wn
    #
    wi
    prmlem0.2
    @5
    @15
    @16
    @11
    @18
    @2
    cK
    cprime
    eleq1
    @5
    @10
    @17
    @2
    cK
    cN
    cdvds
    breq1
    notbid
    imbi12d
    mpbiri
    syl5
    adantrd
    a1i
    @14
    @2
    @13
    wceq
    #
    @2
    @13
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    wo
    @4
    @12
    @13
    @2
    uzp1
    @4
    @19
    @12
    @22
    @4
    @19
    @12
    @4
    @19
    wa
    #
    @8
    @11
    @9
    @23
    @8
    @13
    @7
    wcel
    #
    @11
    @19
    @8
    @24
    wb
    @4
    @2
    @13
    @7
    eleq1
    adantl
    @4
    @24
    @11
    wi
    @19
    @24
    @13
    cprime
    wcel
    #
    @13
    c2
    wne
    #
    wa
    @4
    @11
    @13
    cprime
    c2
    eldifsn
    @4
    @25
    @26
    @11
    @4
    @25
    wa
    #
    @10
    @13
    c2
    @27
    @13
    c2
    wceq
    @10
    @27
    c2
    @13
    @27
    c2
    @13
    cdvds
    wbr
    #
    c2
    @13
    wceq
    #
    @4
    @28
    @25
    @4
    cK
    cz
    wcel
    #
    @1
    @28
    @3
    @30
    @1
    cK
    @2
    eluzel2
    adantl
    #
    @1
    @3
    simpl
    #
    @30
    @1
    wa
    c1
    cz
    wcel
    c2
    c1
    cdvds
    wbr
    wn
    @28
    1z
    n2dvds1
    cK
    c1
    opoe
    mpanr12
    syl2anc
    adantr
    @4
    c2
    c2
    cuz
    cfv
    wcel
    #
    @25
    @28
    @29
    wb
    c2
    cz
    wcel
    #
    @33
    @4
    2z
    c2
    uzid
    mp1i
    @13
    c2
    dvdsprm
    sylan
    mpbid
    eqcomd
    a1d
    necon3ad
    expimpd
    syl5bi
    adantr
    sylbid
    adantrd
    ex
    @4
    @22
    @2
    cM
    cuz
    cfv
    #
    wcel
    #
    @12
    @4
    @21
    @35
    @2
    @4
    @20
    cM
    cuz
    @4
    @20
    cK
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    cM
    @4
    cK
    cc
    wcel
    #
    @20
    @38
    wceq
    #
    @4
    cK
    @31
    zcnd
    @39
    c1
    cc
    wcel
    #
    @41
    @40
    ax-1cn
    ax-1cn
    cK
    c1
    c1
    addass
    mp3an23
    syl
    @38
    cK
    c2
    caddc
    co
    #
    cM
    @37
    c2
    cK
    caddc
    1p1e2
    oveq2i
    prmlem0.3
    eqtri
    syl6eq
    fveq2d
    eleq2d
    @4
    c2
    cM
    cdvds
    wbr
    #
    wn
    #
    @36
    @12
    wi
    @4
    @0
    @43
    @32
    @4
    @0
    c2
    @42
    cdvds
    wbr
    #
    @43
    @4
    @34
    @30
    @0
    @45
    wb
    2z
    @31
    c2
    cK
    dvdsaddr
    sylancr
    @42
    cM
    c2
    cdvds
    prmlem0.3
    breq2i
    syl6bb
    mtbid
    @44
    @36
    @12
    prmlem0.1
    ex
    syl
    sylbid
    jaod
    syl5
    @3
    @5
    @14
    wo
    @1
    cK
    @2
    uzp1
    adantl
    mpjaod
end
