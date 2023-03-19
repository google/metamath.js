include "cv.mm"
include "wpss.mm"
include "wtr.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wceq.mm"
include "wo.mm"
include "wss.mm"
include "wn.mm"
include "inss1.mm"
include "sseli.mm"
include "wel.mm"
include "wral.mm"
include "cvv.mm"
include "dfon2lem3.mm"
include "ax-mp.mm"
include "simprd.mm"
include "eleq1.mm"
include "eleq2.mm"
include "bitrd.mm"
include "notbid.mm"
include "rspccv.mm"
include "syl.mm"
include "adantr.mm"
include "syl5.mm"
include "pm2.01d.mm"
include "elin.mm"
include "sylnib.mm"
include "simpld.mm"
include "trin.mm"
include "syl2an.mm"
include "inex1.mm"
include "psseq1.mm"
include "treq.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "spcv.mm"
include "mpan2d.mm"
include "adantl.mm"
include "anim12d.mm"
include "mtod.mm"
include "ianor.mm"
include "sylib.mm"
include "sspss.mm"
include "mpbi.mm"
include "inss2.mm"
include "orel1.mm"
include "orc.mm"
include "syl6.mm"
include "olc.mm"
include "jaoa.mm"
include "mp2ani.mm"
include "df-ss.mm"
include "sseqin2.mm"
include "orbi12i.mm"
include "sylibr.mm"

theorem dfon2lem4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume dfon2lem4.1: |- A e. _V
  assume dfon2lem4.2: |- B e. _V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  assert |- ( ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) /\ A. y ( ( y C. B /\ Tr y ) -> y e. B ) ) -> ( A C_ B \/ B C_ A ) )

  proof
    vx
    cv
    #
    cA
    wpss
    #
    @0
    wtr
    #
    wa
    #
    @0
    cA
    wcel
    #
    wi
    #
    vx
    wal
    #
    vy
    cv
    #
    cB
    wpss
    #
    @7
    wtr
    #
    wa
    #
    @7
    cB
    wcel
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    cA
    cB
    cin
    #
    cA
    wceq
    #
    @15
    cB
    wceq
    #
    wo
    #
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wo
    @14
    @15
    cA
    wpss
    #
    wn
    #
    @15
    cB
    wpss
    #
    wn
    #
    wo
    #
    @18
    @14
    @21
    @23
    wa
    #
    wn
    @25
    @14
    @26
    @15
    cA
    wcel
    #
    @15
    cB
    wcel
    #
    wa
    #
    @14
    @15
    @15
    wcel
    #
    @29
    @14
    @30
    @30
    @27
    @14
    @30
    wn
    #
    @15
    cA
    @15
    cA
    cB
    inss1
    #
    sseli
    @6
    @27
    @31
    wi
    #
    @13
    @6
    vz
    vz
    wel
    #
    wn
    #
    vz
    cA
    wral
    #
    @33
    @6
    cA
    wtr
    #
    @36
    cA
    cvv
    wcel
    @6
    @37
    @36
    wa
    wi
    dfon2lem4.1
    vx
    vz
    cA
    cvv
    dfon2lem3
    ax-mp
    #
    simprd
    @35
    @31
    vz
    @15
    cA
    vz
    cv
    #
    @15
    wceq
    #
    @34
    @30
    @40
    @34
    @15
    @39
    wcel
    @30
    @39
    @15
    @39
    eleq1
    @39
    @15
    @15
    eleq2
    bitrd
    notbid
    rspccv
    syl
    adantr
    syl5
    pm2.01d
    @15
    cA
    cB
    elin
    sylnib
    @14
    @21
    @27
    @23
    @28
    @14
    @21
    @15
    wtr
    #
    @27
    @6
    @37
    cB
    wtr
    #
    @41
    @13
    @6
    @37
    @36
    @38
    simpld
    @13
    @42
    @35
    vz
    cB
    wral
    #
    cB
    cvv
    wcel
    @13
    @42
    @43
    wa
    wi
    dfon2lem4.2
    vy
    vz
    cB
    cvv
    dfon2lem3
    ax-mp
    simpld
    cA
    cB
    trin
    syl2an
    #
    @6
    @21
    @41
    wa
    #
    @27
    wi
    #
    @13
    @5
    @46
    vx
    @15
    cA
    cB
    dfon2lem4.1
    inex1
    #
    @0
    @15
    wceq
    #
    @3
    @45
    @4
    @27
    @48
    @1
    @21
    @2
    @41
    @0
    @15
    cA
    psseq1
    @0
    @15
    treq
    anbi12d
    @0
    @15
    cA
    eleq1
    imbi12d
    spcv
    adantr
    mpan2d
    @14
    @23
    @41
    @28
    @44
    @13
    @23
    @41
    wa
    #
    @28
    wi
    #
    @6
    @12
    @50
    vy
    @15
    @47
    @7
    @15
    wceq
    #
    @10
    @49
    @11
    @28
    @51
    @8
    @23
    @9
    @41
    @7
    @15
    cB
    psseq1
    @7
    @15
    treq
    anbi12d
    @7
    @15
    cB
    eleq1
    imbi12d
    spcv
    adantl
    mpan2d
    anim12d
    mtod
    @21
    @23
    ianor
    sylib
    @25
    @21
    @16
    wo
    #
    @23
    @17
    wo
    #
    @18
    @15
    cA
    wss
    @52
    @32
    @15
    cA
    sspss
    mpbi
    @15
    cB
    wss
    @53
    cA
    cB
    inss2
    @15
    cB
    sspss
    mpbi
    @22
    @52
    @18
    @24
    @53
    @22
    @52
    @16
    @18
    @21
    @16
    orel1
    @16
    @17
    orc
    syl6
    @24
    @53
    @17
    @18
    @23
    @17
    orel1
    @17
    @16
    olc
    syl6
    jaoa
    mp2ani
    syl
    @19
    @16
    @20
    @17
    cA
    cB
    df-ss
    cB
    cA
    sseqin2
    orbi12i
    sylibr
end
