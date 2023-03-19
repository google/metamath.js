include "cv.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "c1.mm"
include "cr.mm"
include "wi.mm"
include "1rp.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rexralbidv.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "caddc.mm"
include "cz.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "uzid.mm"
include "syl.mm"
include "simpl.mm"
include "ralimi.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspcva.mm"
include "syl2an.mm"
include "abscl.mm"
include "1re.mm"
include "readdcl.mm"
include "sylancl.mm"
include "cle.mm"
include "simpr.mm"
include "simplr.mm"
include "abs2dif.mm"
include "syl2anc.mm"
include "resubcld.mm"
include "subcld.mm"
include "lelttr.mm"
include "mp3an3.mm"
include "mpand.mm"
include "wb.mm"
include "ltsubadd2.mm"
include "sylibd.mm"
include "expimpd.mm"
include "ralimdv.mm"
include "impancom.mm"
include "mpd.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "ex.mm"
include "reximia.mm"
include "rexcom.mm"
include "sylib.mm"

theorem caubnd2
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vw: setvar w
  let vz: setvar z
  let cN: class N
  let cW: class W
  assume cau3.1: |- Z = ( ZZ>= ` M )

  disjoint j k
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint Z y
  disjoint j m
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k w
  disjoint k z
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint M w
  disjoint N j
  disjoint N k
  disjoint N x
  disjoint Z w
  disjoint Z z
  disjoint W j
  disjoint W k
  disjoint W x
  assert |- ( A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( ( F ` k ) e. CC /\ ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x ) -> E. y e. RR E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` ( F ` k ) ) < y )

  proof
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @1
    vj
    cv
    #
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wa
    #
    vk
    @3
    cuz
    cfv
    #
    wral
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @2
    @6
    c1
    clt
    wbr
    #
    wa
    #
    vk
    @10
    wral
    #
    vj
    cZ
    wrex
    #
    @1
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    vk
    @10
    wral
    #
    vj
    cZ
    wrex
    vy
    cr
    wrex
    #
    c1
    crp
    wcel
    @12
    @16
    wi
    1rp
    @11
    @16
    vx
    c1
    crp
    @7
    c1
    wceq
    #
    @9
    @14
    vj
    vk
    cZ
    @10
    @22
    @8
    @13
    @2
    @7
    c1
    @6
    clt
    breq2
    anbi2d
    rexralbidv
    rspcv
    ax-mp
    @16
    @20
    vy
    cr
    wrex
    #
    vj
    cZ
    wrex
    @21
    @15
    @23
    vj
    cZ
    @3
    cZ
    wcel
    #
    @15
    @23
    @24
    @15
    wa
    #
    @4
    cabs
    cfv
    #
    c1
    caddc
    co
    #
    cr
    wcel
    #
    @17
    @27
    clt
    wbr
    #
    vk
    @10
    wral
    #
    @23
    @25
    @26
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @28
    @25
    @4
    cc
    wcel
    #
    @31
    @24
    @3
    @10
    wcel
    #
    @2
    vk
    @10
    wral
    @33
    @15
    @24
    @3
    cz
    wcel
    #
    @34
    @35
    @3
    cM
    cuz
    cfv
    cZ
    cM
    @3
    eluzelz
    cau3.1
    eleq2s
    @3
    uzid
    syl
    @14
    @2
    vk
    @10
    @2
    @13
    simpl
    ralimi
    @2
    @33
    vk
    @3
    @10
    @0
    @3
    wceq
    @1
    @4
    cc
    @0
    @3
    cF
    fveq2
    eleq1d
    rspcva
    syl2an
    #
    @4
    abscl
    #
    syl
    1re
    @26
    c1
    readdcl
    sylancl
    @25
    @33
    @30
    @36
    @24
    @33
    @15
    @30
    @24
    @33
    wa
    #
    @14
    @29
    vk
    @10
    @38
    @2
    @13
    @29
    @38
    @2
    wa
    #
    @13
    @17
    @26
    cmin
    co
    #
    c1
    clt
    wbr
    #
    @29
    @39
    @40
    @6
    cle
    wbr
    #
    @13
    @41
    @39
    @2
    @33
    @42
    @38
    @2
    simpr
    #
    @24
    @33
    @2
    simplr
    #
    @1
    @4
    abs2dif
    syl2anc
    @39
    @40
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @42
    @13
    wa
    @41
    wi
    #
    @39
    @17
    @26
    @39
    @2
    @17
    cr
    wcel
    #
    @43
    @1
    abscl
    syl
    #
    @39
    @33
    @31
    @44
    @37
    syl
    #
    resubcld
    @39
    @5
    cc
    wcel
    @46
    @39
    @1
    @4
    @43
    @44
    subcld
    @5
    abscl
    syl
    @45
    @46
    @32
    @47
    1re
    @40
    @6
    c1
    lelttr
    mp3an3
    syl2anc
    mpand
    @39
    @48
    @31
    @41
    @29
    wb
    #
    @49
    @50
    @48
    @31
    @32
    @51
    1re
    @17
    @26
    c1
    ltsubadd2
    mp3an3
    syl2anc
    sylibd
    expimpd
    ralimdv
    impancom
    mpd
    @20
    @30
    vy
    @27
    cr
    @18
    @27
    wceq
    @19
    @29
    vk
    @10
    @18
    @27
    @17
    clt
    breq2
    ralbidv
    rspcev
    syl2anc
    ex
    reximia
    @20
    vj
    vy
    cZ
    cr
    rexcom
    sylib
    syl
end
