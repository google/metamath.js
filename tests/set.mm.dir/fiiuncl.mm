include "c0.mm"
include "wne.mm"
include "ciun.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "neeq1.mm"
include "iuneq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "neirr.mm"
include "pm2.21i.mm"
include "a1i.mm"
include "cdif.mm"
include "wss.mm"
include "wa.mm"
include "csb.mm"
include "iunxun.mm"
include "nfcsb1v.mm"
include "vex.mm"
include "csbeq1a.mm"
include "iunxsnf.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "0iun.mm"
include "eqtrd.mm"
include "uneq1d.mm"
include "0un.mm"
include "unidm.mm"
include "eqtr4i.mm"
include "adantl.mm"
include "simpl.mm"
include "eldifi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfel.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "chvar.mm"
include "syl5eqel.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "wn.mm"
include "simplll.mm"
include "ad3antlr.mm"
include "neqne.mm"
include "mpd.mm"
include "adantll.mm"
include "w3a.mm"
include "3adant3.mm"
include "simp3.mm"
include "simp1.mm"
include "3jca.mm"
include "3anbi3d.mm"
include "uneq2.mm"
include "imbi2d.mm"
include "3anbi2d.mm"
include "uneq1.mm"
include "vtoclg.mm"
include "syl3c.mm"
include "syl3anc.mm"
include "pm2.61dan.mm"
include "a1d.mm"
include "ex.mm"
include "adantrl.mm"
include "findcard2d.mm"

theorem fiiuncl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume fiiuncl.xph: |- F/ x ph
  assume fiiuncl.b: |- ( ( ph /\ x e. A ) -> B e. D )
  assume fiiuncl.un: |- ( ( ph /\ y e. D /\ z e. D ) -> ( y u. z ) e. D )
  assume fiiuncl.a: |- ( ph -> A e. Fin )
  assume fiiuncl.n0: |- ( ph -> A =/= (/) )

  disjoint A x
  disjoint B y
  disjoint B z
  disjoint y z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint x y
  disjoint x z
  disjoint ph y
  disjoint ph z
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint w y
  disjoint w z
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint u z
  assert |- ( ph -> U_ x e. A B e. D )

  proof
    wph
    cA
    c0
    wne
    #
    vx
    cA
    cB
    ciun
    #
    cD
    wcel
    #
    fiiuncl.n0
    wph
    vv
    cv
    #
    c0
    wne
    #
    vx
    @3
    cB
    ciun
    #
    cD
    wcel
    #
    wi
    c0
    c0
    wne
    #
    vx
    c0
    cB
    ciun
    #
    cD
    wcel
    #
    wi
    #
    vw
    cv
    #
    c0
    wne
    #
    vx
    @11
    cB
    ciun
    #
    cD
    wcel
    #
    wi
    #
    @11
    vu
    cv
    #
    csn
    #
    cun
    #
    c0
    wne
    #
    vx
    @18
    cB
    ciun
    #
    cD
    wcel
    #
    wi
    #
    @0
    @2
    wi
    vv
    vw
    vu
    cA
    @3
    c0
    wceq
    #
    @4
    @7
    @6
    @9
    @3
    c0
    c0
    neeq1
    @23
    @5
    @8
    cD
    vx
    @3
    c0
    cB
    iuneq1
    eleq1d
    imbi12d
    @3
    @11
    wceq
    #
    @4
    @12
    @6
    @14
    @3
    @11
    c0
    neeq1
    @24
    @5
    @13
    cD
    vx
    @3
    @11
    cB
    iuneq1
    eleq1d
    imbi12d
    @3
    @18
    wceq
    #
    @4
    @19
    @6
    @21
    @3
    @18
    c0
    neeq1
    @25
    @5
    @20
    cD
    vx
    @3
    @18
    cB
    iuneq1
    eleq1d
    imbi12d
    @3
    cA
    wceq
    #
    @4
    @0
    @6
    @2
    @3
    cA
    c0
    neeq1
    @26
    @5
    @1
    cD
    vx
    @3
    cA
    cB
    iuneq1
    eleq1d
    imbi12d
    @10
    wph
    @7
    @9
    c0
    neirr
    pm2.21i
    a1i
    wph
    @16
    cA
    @11
    cdif
    wcel
    #
    @15
    @22
    wi
    @11
    cA
    wss
    wph
    @27
    wa
    #
    @15
    @22
    @28
    @15
    wa
    #
    @21
    @19
    @29
    @20
    @13
    vx
    @16
    cB
    csb
    #
    cun
    #
    cD
    @20
    @13
    vx
    @17
    cB
    ciun
    #
    cun
    @31
    vx
    @11
    @17
    cB
    iunxun
    @32
    @30
    @13
    vx
    @16
    cB
    @30
    vx
    @16
    cB
    nfcsb1v
    #
    vu
    vex
    vx
    @16
    cB
    csbeq1a
    #
    iunxsnf
    uneq2i
    eqtri
    @29
    @11
    c0
    wceq
    #
    @31
    cD
    wcel
    #
    @28
    @35
    @36
    @15
    @28
    @35
    wa
    @31
    @30
    @30
    cun
    #
    cD
    @35
    @31
    @37
    wceq
    @28
    @35
    @31
    c0
    @30
    cun
    #
    @37
    @35
    @13
    c0
    @30
    @35
    @13
    @8
    c0
    vx
    @11
    c0
    cB
    iuneq1
    @8
    c0
    wceq
    @35
    vx
    cB
    0iun
    a1i
    eqtrd
    uneq1d
    @38
    @37
    wceq
    @35
    @38
    @30
    @37
    @30
    0un
    @30
    unidm
    #
    eqtr4i
    a1i
    eqtrd
    adantl
    @28
    @37
    cD
    wcel
    #
    @35
    @28
    wph
    @16
    cA
    wcel
    #
    @40
    wph
    @27
    simpl
    @27
    @41
    wph
    @16
    cA
    @11
    eldifi
    #
    adantl
    wph
    @41
    wa
    #
    @37
    @30
    cD
    @39
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    cD
    wcel
    #
    wi
    @43
    @30
    cD
    wcel
    #
    wi
    vx
    vu
    @43
    @48
    vx
    wph
    @41
    vx
    fiiuncl.xph
    @41
    vx
    nfv
    nfan
    vx
    @30
    cD
    @33
    vx
    cD
    nfcv
    nfel
    nfim
    @44
    @16
    wceq
    #
    @46
    @43
    @47
    @48
    @49
    @45
    @41
    wph
    @44
    @16
    cA
    eleq1
    anbi2d
    @49
    cB
    @30
    cD
    @34
    eleq1d
    imbi12d
    fiiuncl.b
    chvar
    #
    syl5eqel
    syl2anc
    adantr
    eqeltrd
    adantlr
    @29
    @35
    wn
    #
    wa
    wph
    @41
    @14
    @36
    wph
    @27
    @15
    @51
    simplll
    @27
    @41
    wph
    @15
    @51
    @42
    ad3antlr
    @15
    @51
    @14
    @28
    @15
    @51
    wa
    @12
    @14
    @51
    @12
    @15
    @11
    c0
    neqne
    adantl
    @15
    @51
    simpl
    mpd
    adantll
    wph
    @41
    @14
    w3a
    #
    @48
    @14
    wph
    @14
    @48
    w3a
    #
    @36
    wph
    @41
    @48
    @14
    @50
    3adant3
    #
    wph
    @41
    @14
    simp3
    #
    @52
    wph
    @14
    @48
    wph
    @41
    @14
    simp1
    @55
    @54
    3jca
    @14
    wph
    @14
    vz
    cv
    #
    cD
    wcel
    #
    w3a
    #
    @13
    @56
    cun
    #
    cD
    wcel
    #
    wi
    #
    wi
    @14
    @53
    @36
    wi
    #
    wi
    vz
    @30
    cD
    @56
    @30
    wceq
    #
    @61
    @62
    @14
    @63
    @58
    @53
    @60
    @36
    @63
    @57
    @48
    wph
    @14
    @56
    @30
    cD
    eleq1
    3anbi3d
    @63
    @59
    @31
    cD
    @56
    @30
    @13
    uneq2
    eleq1d
    imbi12d
    imbi2d
    wph
    vy
    cv
    #
    cD
    wcel
    #
    @57
    w3a
    #
    @64
    @56
    cun
    #
    cD
    wcel
    #
    wi
    @61
    vy
    @13
    cD
    @64
    @13
    wceq
    #
    @66
    @58
    @68
    @60
    @69
    @65
    @14
    wph
    @57
    @64
    @13
    cD
    eleq1
    3anbi2d
    @69
    @67
    @59
    cD
    @64
    @13
    @56
    uneq1
    eleq1d
    imbi12d
    fiiuncl.un
    vtoclg
    vtoclg
    syl3c
    syl3anc
    pm2.61dan
    syl5eqel
    a1d
    ex
    adantrl
    fiiuncl.a
    findcard2d
    mpd
end
