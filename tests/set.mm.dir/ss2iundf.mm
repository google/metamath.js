include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "wceq.mm"
include "nfcri.mm"
include "nfan.mm"
include "simpr.mm"
include "eleq1d.mm"
include "biimprd.mm"
include "wb.mm"
include "w3a.mm"
include "sseq2d.mm"
include "3expa.mm"
include "notbid.mm"
include "biimpd.mm"
include "imim12d.mm"
include "ex.mm"
include "alrimi.mm"
include "nfel.mm"
include "nfss.mm"
include "nfn.mm"
include "nfim.mm"
include "spcimgft.mm"
include "sylc.mm"
include "mpid.mm"
include "syl5bi.mm"
include "con2d.mm"
include "dfrex2.mm"
include "syl6ibr.mm"
include "mpd.mm"
include "ralrimi.mm"
include "ssel.mm"
include "reximi.mm"
include "r19.37.mm"
include "syl.mm"
include "eliun.mm"
include "ssrdv.mm"
include "ralimi.mm"
include "cab.mm"
include "df-iun.mm"
include "sseq1i.mm"
include "abss.mm"
include "dfss2.mm"
include "ralbii.mm"
include "ralcom4.mm"
include "nfiun.mm"
include "r19.23.mm"
include "albii.mm"
include "3bitrri.mm"
include "3bitri.mm"
include "sylibr.mm"

theorem ss2iundf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cG: class G
  let cY: class Y
  let vz: setvar z
  assume ss2iundf.xph: |- F/ x ph
  assume ss2iundf.yph: |- F/ y ph
  assume ss2iundf.y: |- F/_ y Y
  assume ss2iundf.a: |- F/_ y A
  assume ss2iundf.b: |- F/_ y B
  assume ss2iundf.xc: |- F/_ x C
  assume ss2iundf.yc: |- F/_ y C
  assume ss2iundf.d: |- F/_ x D
  assume ss2iundf.g: |- F/_ y G
  assume ss2iundf.el: |- ( ( ph /\ x e. A ) -> Y e. C )
  assume ss2iundf.sub: |- ( ( ph /\ x e. A /\ y = Y ) -> D = G )
  assume ss2iundf.ss: |- ( ( ph /\ x e. A ) -> B C_ G )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  assert |- ( ph -> U_ x e. A B C_ U_ y e. C D )

  proof
    wph
    cB
    cD
    wss
    #
    vy
    cC
    wrex
    #
    vx
    cA
    wral
    #
    vx
    cA
    cB
    ciun
    #
    vy
    cC
    cD
    ciun
    #
    wss
    #
    wph
    @1
    vx
    cA
    ss2iundf.xph
    wph
    vx
    cv
    cA
    wcel
    #
    @1
    wph
    @6
    wa
    #
    cB
    cG
    wss
    #
    @1
    ss2iundf.ss
    @7
    @8
    @0
    wn
    #
    vy
    cC
    wral
    #
    wn
    @1
    @7
    @10
    @8
    @10
    vy
    cv
    #
    cC
    wcel
    #
    @9
    wi
    #
    vy
    wal
    #
    @7
    @8
    wn
    #
    @9
    vy
    cC
    df-ral
    @7
    @14
    cY
    cC
    wcel
    #
    @15
    ss2iundf.el
    @7
    @11
    cY
    wceq
    #
    @13
    @16
    @15
    wi
    #
    wi
    #
    wi
    #
    vy
    wal
    @16
    @14
    @18
    wi
    @7
    @20
    vy
    wph
    @6
    vy
    ss2iundf.yph
    vy
    vx
    cA
    ss2iundf.a
    nfcri
    nfan
    @7
    @17
    @19
    @7
    @17
    wa
    #
    @16
    @12
    @9
    @15
    @21
    @12
    @16
    @21
    @11
    cY
    cC
    @7
    @17
    simpr
    eleq1d
    biimprd
    @21
    @9
    @15
    @21
    @0
    @8
    wph
    @6
    @17
    @0
    @8
    wb
    wph
    @6
    @17
    w3a
    cD
    cG
    cB
    ss2iundf.sub
    sseq2d
    3expa
    notbid
    biimpd
    imim12d
    ex
    alrimi
    ss2iundf.el
    @13
    @18
    vy
    cY
    cC
    @16
    @15
    vy
    vy
    cY
    cC
    ss2iundf.y
    ss2iundf.yc
    nfel
    @8
    vy
    vy
    cB
    cG
    ss2iundf.b
    ss2iundf.g
    nfss
    nfn
    nfim
    ss2iundf.y
    spcimgft
    sylc
    mpid
    syl5bi
    con2d
    @0
    vy
    cC
    dfrex2
    syl6ibr
    mpd
    ex
    ralrimi
    @2
    cB
    @4
    wss
    #
    vx
    cA
    wral
    #
    @5
    @1
    @22
    vx
    cA
    @1
    vz
    cB
    @4
    @1
    vz
    cv
    #
    cB
    wcel
    #
    @24
    cD
    wcel
    #
    vy
    cC
    wrex
    #
    @24
    @4
    wcel
    #
    @1
    @25
    @26
    wi
    #
    vy
    cC
    wrex
    @25
    @27
    wi
    @0
    @29
    vy
    cC
    cB
    cD
    @24
    ssel
    reximi
    @25
    @26
    vy
    cC
    vy
    vz
    cB
    ss2iundf.b
    nfcri
    r19.37
    syl
    vy
    @24
    cC
    cD
    eliun
    syl6ibr
    ssrdv
    ralimi
    @5
    @25
    vx
    cA
    wrex
    #
    vz
    cab
    #
    @4
    wss
    @30
    @28
    wi
    #
    vz
    wal
    #
    @23
    @3
    @31
    @4
    vx
    vz
    cA
    cB
    df-iun
    sseq1i
    @30
    vz
    @4
    abss
    @23
    @25
    @28
    wi
    #
    vz
    wal
    #
    vx
    cA
    wral
    @34
    vx
    cA
    wral
    #
    vz
    wal
    @33
    @22
    @35
    vx
    cA
    vz
    cB
    @4
    dfss2
    ralbii
    @34
    vx
    vz
    cA
    ralcom4
    @36
    @32
    vz
    @25
    @28
    vx
    cA
    vx
    vz
    @4
    vy
    vx
    cC
    cD
    ss2iundf.xc
    ss2iundf.d
    nfiun
    nfcri
    r19.23
    albii
    3bitrri
    3bitri
    sylibr
    syl
end
