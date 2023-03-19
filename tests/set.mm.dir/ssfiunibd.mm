include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "wrex.mm"
include "cab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "simpll.mm"
include "wex.mm"
include "19.8a.mm"
include "ancoms.mm"
include "eluni.mm"
include "sylibr.mm"
include "adantll.mm"
include "syl2anc.mm"
include "eqid.mm"
include "upbdrech2.mm"
include "simpld.mm"
include "ralrimiva.mm"
include "fimaxre3.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfsup.mm"
include "nfif.mm"
include "nfbr.mm"
include "nfral.mm"
include "nfan.mm"
include "sselda.mm"
include "sylib.mm"
include "exancom.mm"
include "df-rex.mm"
include "ad4ant14.mm"
include "nfra1.mm"
include "wi.mm"
include "w3a.mm"
include "3impa.mm"
include "3adant1r.mm"
include "wn.mm"
include "n0i.mm"
include "adantl.mm"
include "iffalsed.mm"
include "eqcomd.mm"
include "3adant1.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "simp1lr.mm"
include "wss.mm"
include "wne.mm"
include "nfab1.mm"
include "abid.mm"
include "biimpi.mm"
include "nfsab.mm"
include "simp3.mm"
include "3exp.mm"
include "adantr.mm"
include "rexlimd.mm"
include "mpd.mm"
include "ex.mm"
include "ssrd.mm"
include "elabrexg.mm"
include "ne0i.mm"
include "syl.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "cbvabv.mm"
include "eleq2s.mm"
include "rspa.mm"
include "eqbrtrd.mm"
include "reximdv.mm"
include "suprub.mm"
include "syl31anc.mm"
include "3adant1l.mm"
include "letrd.mm"
include "ralrimi.mm"
include "reximdva.mm"

theorem ssfiunibd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let vu: setvar u
  let vv: setvar v
  assume ssfiunibd.fi: |- ( ph -> A e. Fin )
  assume ssfiunibd.b: |- ( ( ph /\ z e. U. A ) -> B e. RR )
  assume ssfiunibd.bd: |- ( ( ph /\ x e. A ) -> E. y e. RR A. z e. x B <_ y )
  assume ssfiunibd.ssun: |- ( ph -> C C_ U. A )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint w x
  disjoint w z
  disjoint B x
  disjoint B y
  disjoint B w
  disjoint C x
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ph w
  disjoint A u
  disjoint A v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint u w
  disjoint B u
  disjoint B v
  disjoint ph u
  disjoint ph v
  assert |- ( ph -> E. w e. RR A. z e. C B <_ w )

  proof
    wph
    vx
    cv
    #
    c0
    wceq
    #
    cc0
    vu
    cv
    #
    cB
    wceq
    #
    vz
    @0
    wrex
    #
    vu
    cab
    #
    cr
    clt
    csup
    #
    cif
    #
    vw
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vw
    cr
    wrex
    #
    cB
    @8
    cle
    wbr
    #
    vz
    cC
    wral
    #
    vw
    cr
    wrex
    wph
    cA
    cfn
    wcel
    @7
    cr
    wcel
    #
    vx
    cA
    wral
    @11
    ssfiunibd.fi
    wph
    @14
    vx
    cA
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @14
    cB
    @7
    cle
    wbr
    vz
    @0
    wral
    @16
    vz
    vy
    vu
    @0
    cB
    @7
    @16
    vz
    cv
    #
    @0
    wcel
    #
    wa
    wph
    @17
    cA
    cuni
    #
    wcel
    #
    cB
    cr
    wcel
    #
    wph
    @15
    @18
    simpll
    @15
    @18
    @20
    wph
    @15
    @18
    wa
    #
    @18
    @15
    wa
    #
    vx
    wex
    #
    @20
    @18
    @15
    @24
    @23
    vx
    19.8a
    ancoms
    vx
    @17
    cA
    eluni
    #
    sylibr
    adantll
    ssfiunibd.b
    syl2anc
    #
    ssfiunibd.bd
    @7
    eqid
    upbdrech2
    simpld
    #
    ralrimiva
    vw
    vx
    cA
    @7
    fimaxre3
    syl2anc
    wph
    @10
    @13
    vw
    cr
    wph
    @8
    cr
    wcel
    #
    wa
    #
    @10
    @13
    @29
    @10
    wa
    #
    @12
    vz
    cC
    @29
    @10
    vz
    @29
    vz
    nfv
    @9
    vz
    vx
    cA
    vz
    cA
    nfcv
    vz
    @7
    @8
    cle
    @1
    vz
    cc0
    @6
    @1
    vz
    nfv
    vz
    cc0
    nfcv
    vz
    @5
    cr
    clt
    @4
    vz
    vu
    @3
    vz
    @0
    nfre1
    #
    nfab
    vz
    cr
    nfcv
    vz
    clt
    nfcv
    nfsup
    nfif
    vz
    cle
    nfcv
    vz
    @8
    nfcv
    nfbr
    nfral
    nfan
    @30
    @17
    cC
    wcel
    #
    @12
    @30
    @32
    wa
    #
    @18
    vx
    cA
    wrex
    #
    @12
    wph
    @32
    @34
    @28
    @10
    wph
    @32
    wa
    #
    @22
    vx
    wex
    #
    @34
    @35
    @24
    @36
    @35
    @20
    @24
    wph
    cC
    @19
    @17
    ssfiunibd.ssun
    sselda
    @25
    sylib
    @18
    @15
    vx
    exancom
    sylib
    @18
    vx
    cA
    df-rex
    sylibr
    ad4ant14
    @33
    @18
    @12
    vx
    cA
    @30
    @32
    vx
    @29
    @10
    vx
    @29
    vx
    nfv
    @9
    vx
    cA
    nfra1
    nfan
    @32
    vx
    nfv
    nfan
    @12
    vx
    nfv
    @30
    @15
    @18
    @12
    wi
    wi
    @32
    @30
    @15
    @18
    @12
    @30
    @15
    @18
    w3a
    cB
    @6
    @8
    @29
    @15
    @18
    @21
    @10
    wph
    @15
    @18
    @21
    @28
    wph
    @15
    @18
    @21
    @26
    3impa
    #
    3adant1r
    3adant1r
    @29
    @15
    @18
    @6
    cr
    wcel
    #
    @10
    wph
    @15
    @18
    @38
    @28
    wph
    @15
    @18
    w3a
    #
    @6
    @7
    cr
    @15
    @18
    @6
    @7
    wceq
    #
    wph
    @22
    @7
    @6
    @22
    @1
    cc0
    @6
    @18
    @1
    wn
    @15
    @0
    @17
    n0i
    adantl
    iffalsed
    eqcomd
    #
    3adant1
    wph
    @15
    @14
    @18
    @27
    3adant3
    eqeltrd
    3adant1r
    3adant1r
    wph
    @28
    @10
    @15
    @18
    simp1lr
    @29
    @15
    @18
    cB
    @6
    cle
    wbr
    #
    @10
    wph
    @15
    @18
    @42
    @28
    @39
    @5
    cr
    wss
    #
    @5
    c0
    wne
    #
    vv
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vv
    @5
    wral
    #
    vy
    cr
    wrex
    #
    cB
    @5
    wcel
    #
    @42
    wph
    @15
    @43
    @18
    @16
    vu
    @5
    cr
    @16
    vu
    nfv
    @4
    vu
    nfab1
    vu
    cr
    nfcv
    @16
    @2
    @5
    wcel
    #
    @2
    cr
    wcel
    #
    @16
    @51
    wa
    #
    @4
    @52
    @51
    @4
    @16
    @51
    @4
    @4
    vu
    abid
    biimpi
    adantl
    @53
    @3
    @52
    vz
    @0
    @16
    @51
    vz
    @16
    vz
    nfv
    #
    @4
    vz
    vu
    vu
    @31
    nfsab
    nfan
    @52
    vz
    nfv
    @16
    @18
    @3
    @52
    wi
    wi
    @51
    @16
    @18
    @3
    @52
    @16
    @18
    @3
    w3a
    @2
    cB
    cr
    @16
    @18
    @3
    simp3
    @16
    @18
    @21
    @3
    @26
    3adant3
    eqeltrd
    3exp
    adantr
    rexlimd
    mpd
    ex
    ssrd
    3adant3
    @39
    @50
    @44
    @39
    @18
    @21
    @50
    wph
    @15
    @18
    simp3
    @37
    vz
    vu
    @0
    cB
    cr
    elabrexg
    syl2anc
    #
    @5
    cB
    ne0i
    syl
    wph
    @15
    @49
    @18
    @16
    cB
    @46
    cle
    wbr
    #
    vz
    @0
    wral
    #
    vy
    cr
    wrex
    @49
    ssfiunibd.bd
    @16
    @57
    @48
    vy
    cr
    @16
    @57
    @48
    @16
    @57
    wa
    #
    @47
    vv
    @5
    @58
    @45
    @5
    wcel
    #
    wa
    #
    @45
    cB
    wceq
    #
    vz
    @0
    wrex
    #
    @47
    @59
    @62
    @58
    @62
    @45
    @62
    vv
    cab
    #
    @5
    @45
    @63
    wcel
    @62
    @62
    vv
    abid
    biimpi
    @4
    @62
    vu
    vv
    @2
    @45
    wceq
    @3
    @61
    vz
    @0
    @2
    @45
    cB
    eqeq1
    rexbidv
    cbvabv
    eleq2s
    adantl
    @60
    @61
    @47
    vz
    @0
    @58
    @59
    vz
    @16
    @57
    vz
    @54
    @56
    vz
    @0
    nfra1
    nfan
    @4
    vz
    vu
    vv
    @31
    nfsab
    nfan
    @47
    vz
    nfv
    @58
    @18
    @61
    @47
    wi
    wi
    #
    @59
    @57
    @64
    @16
    @57
    @18
    @61
    @47
    @57
    @18
    @61
    w3a
    @45
    cB
    @46
    cle
    @57
    @18
    @61
    simp3
    @57
    @18
    @56
    @61
    @56
    vz
    @0
    rspa
    3adant3
    eqbrtrd
    3exp
    adantl
    adantr
    rexlimd
    mpd
    ralrimiva
    ex
    reximdv
    mpd
    3adant3
    @55
    vy
    vv
    @5
    cB
    suprub
    syl31anc
    3adant1r
    3adant1r
    @10
    @15
    @18
    @6
    @8
    cle
    wbr
    @29
    @10
    @15
    @18
    w3a
    @6
    @7
    @8
    cle
    @15
    @18
    @40
    @10
    @41
    3adant1
    @10
    @15
    @9
    @18
    @9
    vx
    cA
    rspa
    3adant3
    eqbrtrd
    3adant1l
    letrd
    3exp
    adantr
    rexlimd
    mpd
    ex
    ralrimi
    ex
    reximdva
    mpd
end
