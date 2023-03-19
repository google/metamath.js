include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "nfcv.mm"
include "frexr.mm"
include "limsupre3uzlem.mm"
include "wb.mm"
include "wceq.mm"
include "breq1.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "fveq2.mm"
include "rexeqdv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq2d.mm"
include "cbvrex.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvralv.mm"
include "cbvrexv.mm"
include "breq2.mm"
include "raleqdv.mm"
include "breq1d.mm"
include "cbvral.mm"
include "anbi12i.mm"
include "rexbii.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "uzub.mm"
include "wi.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "bicom.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "3bitrd.mm"
include "anbi2d.mm"

theorem limsupreuz
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vl: setvar l
  let vy: setvar y
  assume limsupreuz.1: |- F/_ j F
  assume limsupreuz.2: |- ( ph -> M e. ZZ )
  assume limsupreuz.3: |- Z = ( ZZ>= ` M )
  assume limsupreuz.4: |- ( ph -> F : Z --> RR )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint j x
  disjoint F i
  disjoint F l
  disjoint F y
  disjoint i k
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint k l
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint M i
  disjoint M l
  disjoint Z i
  disjoint Z l
  disjoint Z y
  disjoint i j
  disjoint j l
  disjoint j y
  disjoint i ph
  disjoint l ph
  disjoint ph y
  assert |- ( ph -> ( ( limsup ` F ) e. RR <-> ( E. x e. RR A. k e. Z E. j e. ( ZZ>= ` k ) x <_ ( F ` j ) /\ E. x e. RR A. j e. Z ( F ` j ) <_ x ) ) )

  proof
    wph
    cF
    clsp
    cfv
    cr
    wcel
    #
    vx
    cv
    #
    vj
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vj
    vk
    cv
    #
    cuz
    cfv
    #
    wrex
    #
    vk
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @3
    @1
    cle
    wbr
    #
    vj
    @6
    wral
    #
    vk
    cZ
    wrex
    #
    vx
    cr
    wrex
    #
    wa
    #
    @9
    @10
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    wa
    wph
    @0
    vy
    cv
    #
    vl
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vl
    vi
    cv
    #
    cuz
    cfv
    #
    wrex
    #
    vi
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    @19
    @17
    cle
    wbr
    #
    vl
    @22
    wral
    #
    vi
    cZ
    wrex
    #
    vy
    cr
    wrex
    #
    wa
    #
    @14
    wph
    vy
    vl
    vi
    cF
    cM
    cZ
    vl
    cF
    nfcv
    limsupreuz.2
    limsupreuz.3
    wph
    cZ
    cF
    limsupreuz.4
    frexr
    limsupre3uzlem
    @30
    @14
    wb
    wph
    @25
    @9
    @29
    @13
    @24
    @8
    vy
    vx
    cr
    @17
    @1
    wceq
    #
    @24
    @1
    @19
    cle
    wbr
    #
    vl
    @22
    wrex
    #
    vi
    cZ
    wral
    #
    @8
    @31
    @23
    @33
    vi
    cZ
    @31
    @20
    @32
    vl
    @22
    @17
    @1
    @19
    cle
    breq1
    rexbidv
    ralbidv
    @34
    @8
    wb
    @31
    @33
    @7
    vi
    vk
    cZ
    @21
    @5
    wceq
    #
    @33
    @32
    vl
    @6
    wrex
    #
    @7
    @35
    @32
    vl
    @22
    @6
    @21
    @5
    cuz
    fveq2
    #
    rexeqdv
    @36
    @7
    wb
    @35
    @32
    @4
    vl
    vj
    @6
    vj
    @1
    @19
    cle
    vj
    @1
    nfcv
    #
    vj
    cle
    nfcv
    #
    vj
    @18
    cF
    limsupreuz.1
    vj
    @18
    nfcv
    nffv
    #
    nfbr
    @4
    vl
    nfv
    @18
    @2
    wceq
    #
    @19
    @3
    @1
    cle
    @18
    @2
    cF
    fveq2
    #
    breq2d
    cbvrex
    a1i
    bitrd
    cbvralv
    a1i
    bitrd
    cbvrexv
    @28
    @12
    vy
    vx
    cr
    @31
    @28
    @19
    @1
    cle
    wbr
    #
    vl
    @22
    wral
    #
    vi
    cZ
    wrex
    #
    @12
    @31
    @27
    @44
    vi
    cZ
    @31
    @26
    @43
    vl
    @22
    @17
    @1
    @19
    cle
    breq2
    ralbidv
    rexbidv
    @45
    @12
    wb
    @31
    @44
    @11
    vi
    vk
    cZ
    @35
    @44
    @43
    vl
    @6
    wral
    #
    @11
    @35
    @43
    vl
    @22
    @6
    @37
    raleqdv
    @46
    @11
    wb
    @35
    @43
    @10
    vl
    vj
    @6
    vj
    @19
    @1
    cle
    @40
    @39
    @38
    nfbr
    @10
    vl
    nfv
    @41
    @19
    @3
    @1
    cle
    @42
    breq1d
    cbvral
    a1i
    bitrd
    cbvrexv
    a1i
    bitrd
    cbvrexv
    anbi12i
    a1i
    bitrd
    wph
    @13
    @16
    @9
    wph
    @13
    @21
    cF
    cfv
    #
    @1
    cle
    wbr
    #
    vi
    @6
    wral
    #
    vk
    cZ
    wrex
    #
    vx
    cr
    wrex
    #
    @48
    vi
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @16
    @13
    @51
    wb
    wph
    @12
    @50
    vx
    cr
    @11
    @49
    vk
    cZ
    @10
    @48
    vj
    vi
    @6
    @10
    vi
    nfv
    #
    vj
    @47
    @1
    cle
    vj
    @21
    cF
    limsupreuz.1
    vj
    @21
    nfcv
    nffv
    @39
    @38
    nfbr
    #
    @2
    @21
    wceq
    #
    @3
    @47
    @1
    cle
    @2
    @21
    cF
    fveq2
    breq1d
    #
    cbvral
    rexbii
    rexbii
    a1i
    wph
    vx
    @47
    vi
    vk
    cM
    cZ
    wph
    vi
    nfv
    limsupreuz.2
    limsupreuz.3
    wph
    @21
    cZ
    wcel
    #
    wa
    cZ
    cr
    @21
    cF
    wph
    cZ
    cr
    cF
    wf
    @58
    limsupreuz.4
    adantr
    wph
    @58
    simpr
    ffvelrnd
    uzub
    @53
    @16
    wb
    wph
    @52
    @15
    vx
    cr
    @48
    @10
    vi
    vj
    cZ
    @55
    @54
    @56
    @10
    @48
    wb
    #
    wi
    #
    @21
    @2
    wceq
    #
    @48
    @10
    wb
    #
    wi
    #
    @57
    @60
    @61
    @59
    wi
    @63
    @56
    @61
    @59
    @2
    @21
    eqcom
    imbi1i
    @59
    @62
    @61
    @10
    @48
    bicom
    imbi2i
    bitri
    mpbi
    cbvral
    rexbii
    a1i
    3bitrd
    anbi2d
    bitrd
end
