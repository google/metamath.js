include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "wb.mm"
include "wceq.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "cbvrexv.mm"
include "a1i.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "bitrd.mm"
include "biimpi.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "nfv.mm"
include "nfan.mm"
include "nfra1.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfcv.mm"
include "nfsup.mm"
include "nfbr.mm"
include "nfif.mm"
include "cz.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "eqid.mm"
include "simplr.mm"
include "ad5ant15.mm"
include "simpr.mm"
include "uzublem.mm"
include "ex.mm"
include "rexlimdva.mm"
include "imp.mm"
include "sylan2.mm"
include "uzidd2.mm"
include "ad2antrr.mm"
include "raleqi.mm"
include "adantl.mm"
include "rspce.mm"
include "syl2anc.mm"
include "reximdva.mm"
include "impbid.mm"
include "3bitrd.mm"

theorem uzub
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vw: setvar w
  let vy: setvar y
  assume uzub.1: |- F/ j ph
  assume uzub.2: |- ( ph -> M e. ZZ )
  assume uzub.3: |- Z = ( ZZ>= ` M )
  assume uzub.12: |- ( ( ph /\ j e. Z ) -> B e. RR )

  disjoint B k
  disjoint B x
  disjoint k x
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint j x
  disjoint B i
  disjoint B w
  disjoint i k
  disjoint i w
  disjoint i x
  disjoint k w
  disjoint w x
  disjoint B y
  disjoint i y
  disjoint w y
  disjoint M i
  disjoint M w
  disjoint i j
  disjoint j w
  disjoint Z i
  disjoint Z w
  disjoint Z y
  disjoint j y
  disjoint i ph
  disjoint ph w
  disjoint ph y
  assert |- ( ph -> ( E. x e. RR E. k e. Z A. j e. ( ZZ>= ` k ) B <_ x <-> E. x e. RR A. j e. Z B <_ x ) )

  proof
    wph
    cB
    vx
    cv
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
    cB
    vw
    cv
    #
    cle
    wbr
    #
    vj
    vi
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vi
    cZ
    wrex
    #
    vw
    cr
    wrex
    #
    @8
    vj
    cZ
    wral
    #
    vw
    cr
    wrex
    #
    @1
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @6
    @13
    wb
    wph
    @5
    @12
    vx
    vw
    cr
    @0
    @7
    wceq
    #
    @5
    @1
    vj
    @10
    wral
    #
    vi
    cZ
    wrex
    #
    @12
    @5
    @20
    wb
    @18
    @4
    @19
    vk
    vi
    cZ
    @2
    @9
    wceq
    @1
    vj
    @3
    @10
    @2
    @9
    cuz
    fveq2
    raleqdv
    cbvrexv
    a1i
    @18
    @19
    @11
    vi
    cZ
    @18
    @1
    @8
    vj
    @10
    @0
    @7
    cB
    cle
    breq2
    ralbidv
    rexbidv
    bitrd
    cbvrexv
    a1i
    wph
    @13
    @15
    wph
    @13
    @15
    @13
    wph
    cB
    vy
    cv
    #
    cle
    wbr
    #
    vj
    @10
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
    @15
    @13
    @25
    @12
    @24
    vw
    vy
    cr
    @7
    @21
    wceq
    #
    @11
    @23
    vi
    cZ
    @26
    @8
    @22
    vj
    @10
    @7
    @21
    cB
    cle
    breq2
    ralbidv
    rexbidv
    cbvrexv
    biimpi
    wph
    @25
    @15
    wph
    @24
    @15
    vy
    cr
    wph
    @21
    cr
    wcel
    #
    wa
    #
    @24
    @15
    @28
    @24
    @15
    @28
    @23
    @15
    vi
    cZ
    @28
    @9
    cZ
    wcel
    #
    wa
    #
    @23
    @15
    @30
    @23
    wa
    vw
    cB
    vj
    @9
    cM
    vj
    cM
    @9
    cfz
    co
    #
    cB
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    @34
    @21
    cle
    wbr
    #
    @21
    @34
    cif
    #
    @21
    cZ
    @30
    @23
    vj
    @28
    @29
    vj
    wph
    @27
    vj
    uzub.1
    @27
    vj
    nfv
    nfan
    @29
    vj
    nfv
    nfan
    @22
    vj
    @10
    nfra1
    nfan
    @35
    vj
    @21
    @34
    vj
    @34
    @21
    cle
    vj
    @33
    cr
    clt
    vj
    @32
    vj
    @31
    cB
    nfmpt1
    nfrn
    vj
    cr
    nfcv
    vj
    clt
    nfcv
    nfsup
    #
    vj
    cle
    nfcv
    vj
    @21
    nfcv
    #
    nfbr
    @38
    @37
    nfif
    wph
    cM
    cz
    wcel
    @27
    @29
    @23
    uzub.2
    ad3antrrr
    uzub.3
    wph
    @27
    @29
    @23
    simpllr
    @34
    eqid
    @36
    eqid
    @28
    @29
    @23
    simplr
    wph
    vj
    cv
    cZ
    wcel
    cB
    cr
    wcel
    @27
    @29
    @23
    uzub.12
    ad5ant15
    @30
    @23
    simpr
    uzublem
    ex
    rexlimdva
    imp
    ex
    rexlimdva
    imp
    sylan2
    ex
    wph
    @14
    @12
    vw
    cr
    wph
    @7
    cr
    wcel
    #
    wa
    #
    @14
    @12
    @40
    @14
    wa
    cM
    cZ
    wcel
    #
    @8
    vj
    cM
    cuz
    cfv
    #
    wral
    #
    @12
    wph
    @41
    @39
    @14
    wph
    cM
    cZ
    uzub.2
    uzub.3
    uzidd2
    ad2antrr
    @14
    @43
    @40
    @14
    @43
    @8
    vj
    cZ
    @42
    uzub.3
    raleqi
    biimpi
    adantl
    @11
    @43
    vi
    cM
    cZ
    @43
    vi
    nfv
    @9
    cM
    wceq
    @8
    vj
    @10
    @42
    @9
    cM
    cuz
    fveq2
    raleqdv
    rspce
    syl2anc
    ex
    reximdva
    impbid
    @15
    @17
    wb
    wph
    @14
    @16
    vw
    vx
    cr
    @7
    @0
    wceq
    @8
    @1
    vj
    cZ
    @7
    @0
    cB
    cle
    breq2
    ralbidv
    cbvrexv
    a1i
    3bitrd
end
