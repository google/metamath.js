include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "nfv.mm"
include "nfcv.mm"
include "wss.mm"
include "cuz.mm"
include "uzssre.mm"
include "eqsstri.mm"
include "a1i.mm"
include "frexr.mm"
include "limsupub.mm"
include "adantr.mm"
include "cceil.mm"
include "cif.mm"
include "cfz.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "nfan.mm"
include "nfra1.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfsup.mm"
include "nfbr.mm"
include "nfif.mm"
include "wceq.mm"
include "breq2.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "adantl.mm"
include "simp-4r.mm"
include "syldan.mm"
include "wf.mm"
include "ad4antr.mm"
include "simpllr.mm"
include "simplr.mm"
include "biimpri.mm"
include "syl.mm"
include "eqid.mm"
include "limsupubuzlem.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "wn.mm"
include "c0.mm"
include "uz0.mm"
include "eqtrd.mm"
include "cc0.mm"
include "0red.mm"
include "rzal.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "nffv.mm"
include "cbvral.mm"
include "rexbii.mm"
include "sylib.mm"

theorem limsupubuz
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vk: setvar k
  let vl: setvar l
  let vy: setvar y
  assume limsupubuz.j: |- F/_ j F
  assume limsupubuz.z: |- Z = ( ZZ>= ` M )
  assume limsupubuz.f: |- ( ph -> F : Z --> RR )
  assume limsupubuz.n: |- ( ph -> ( limsup ` F ) =/= +oo )

  disjoint F x
  disjoint M x
  disjoint Z j
  disjoint Z x
  disjoint j x
  disjoint F i
  disjoint F k
  disjoint F l
  disjoint F y
  disjoint i k
  disjoint i l
  disjoint i y
  disjoint k l
  disjoint k y
  disjoint l y
  disjoint k x
  disjoint l x
  disjoint x y
  disjoint M k
  disjoint M l
  disjoint M y
  disjoint Z i
  disjoint Z k
  disjoint Z l
  disjoint Z y
  disjoint j l
  disjoint k ph
  disjoint l ph
  disjoint ph y
  assert |- ( ph -> E. x e. RR A. j e. Z ( F ` j ) <_ x )

  proof
    wph
    vl
    cv
    #
    cF
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vl
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    vj
    cv
    #
    cF
    cfv
    #
    @2
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    wph
    cM
    cz
    wcel
    #
    @5
    wph
    @10
    wa
    #
    vk
    cv
    #
    @0
    cle
    wbr
    #
    @1
    vy
    cv
    #
    cle
    wbr
    #
    wi
    #
    vl
    cZ
    wral
    #
    vk
    cr
    wrex
    #
    vy
    cr
    wrex
    #
    @5
    wph
    @19
    @10
    wph
    vy
    cZ
    vl
    vk
    cF
    wph
    vl
    nfv
    #
    vl
    cF
    nfcv
    cZ
    cr
    wss
    wph
    cZ
    cM
    cuz
    cfv
    #
    cr
    limsupubuz.z
    cM
    uzssre
    eqsstri
    a1i
    wph
    cZ
    cF
    limsupubuz.f
    frexr
    limsupubuz.n
    limsupub
    adantr
    @11
    @18
    @5
    vy
    cr
    @11
    @14
    cr
    wcel
    #
    wa
    #
    @17
    @5
    vk
    cr
    @23
    @12
    cr
    wcel
    #
    @17
    @5
    @23
    @24
    wa
    #
    @17
    wa
    #
    vx
    vl
    cF
    @12
    cM
    @12
    cceil
    cfv
    #
    cM
    cle
    wbr
    cM
    @27
    cif
    #
    vl
    cM
    @28
    cfz
    co
    #
    @1
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    @32
    @14
    cle
    wbr
    #
    @14
    @32
    cif
    #
    @14
    cZ
    @25
    @17
    vl
    @23
    @24
    vl
    @11
    @22
    vl
    wph
    @10
    vl
    @20
    @10
    vl
    nfv
    nfan
    @22
    vl
    nfv
    nfan
    @24
    vl
    nfv
    nfan
    @16
    vl
    cZ
    nfra1
    nfan
    @33
    vl
    @14
    @32
    vl
    @32
    @14
    cle
    vl
    @31
    cr
    clt
    vl
    @30
    vl
    @29
    @1
    nfmpt1
    nfrn
    vl
    cr
    nfcv
    vl
    clt
    nfcv
    nfsup
    #
    vl
    cle
    nfcv
    vl
    @14
    nfcv
    #
    nfbr
    @36
    @35
    nfif
    @25
    @17
    @12
    vi
    cv
    #
    cle
    wbr
    #
    @37
    cF
    cfv
    #
    @14
    cle
    wbr
    #
    wi
    #
    vi
    cZ
    wral
    #
    @10
    @17
    @42
    @25
    @17
    @42
    @16
    @41
    vl
    vi
    cZ
    @0
    @37
    wceq
    #
    @13
    @38
    @15
    @40
    @0
    @37
    @12
    cle
    breq2
    @43
    @1
    @39
    @14
    cle
    @0
    @37
    cF
    fveq2
    breq1d
    imbi12d
    cbvralv
    #
    biimpi
    adantl
    #
    wph
    @10
    @22
    @24
    @42
    simp-4r
    syldan
    limsupubuz.z
    @25
    @17
    @42
    cZ
    cr
    cF
    wf
    #
    @45
    wph
    @46
    @10
    @22
    @24
    @42
    limsupubuz.f
    ad4antr
    syldan
    @25
    @17
    @42
    @22
    @45
    @11
    @22
    @24
    @42
    simpllr
    syldan
    @25
    @17
    @42
    @24
    @45
    @23
    @24
    @42
    simplr
    syldan
    @26
    @42
    @17
    @45
    @17
    @42
    @44
    biimpri
    syl
    @28
    eqid
    @32
    eqid
    @34
    eqid
    limsupubuzlem
    exp31
    rexlimdv
    rexlimdva
    mpd
    @10
    wn
    #
    @5
    wph
    @47
    cZ
    c0
    wceq
    #
    @5
    @47
    cZ
    @21
    c0
    cZ
    @21
    wceq
    @47
    limsupubuz.z
    a1i
    cM
    uz0
    eqtrd
    @48
    cc0
    cr
    wcel
    @1
    cc0
    cle
    wbr
    #
    vl
    cZ
    wral
    #
    @5
    @48
    0red
    @49
    vl
    cZ
    rzal
    @4
    @50
    vx
    cc0
    cr
    @2
    cc0
    wceq
    @3
    @49
    vl
    cZ
    @2
    cc0
    @1
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    syl
    adantl
    pm2.61dan
    @4
    @9
    vx
    cr
    @3
    @8
    vl
    vj
    cZ
    vj
    @1
    @2
    cle
    vj
    @0
    cF
    limsupubuz.j
    vj
    @0
    nfcv
    nffv
    vj
    cle
    nfcv
    vj
    @2
    nfcv
    nfbr
    @8
    vl
    nfv
    @0
    @6
    wceq
    @1
    @7
    @2
    cle
    @0
    @6
    cF
    fveq2
    breq1d
    cbvral
    rexbii
    sylib
end
