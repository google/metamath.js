include "clsp.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cr.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "wral.mm"
include "wi.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "cif.mm"
include "wceq.mm"
include "wss.mm"
include "wb.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrunb1.mm"
include "syl.mm"
include "mpbird.mm"
include "ifcl.mm"
include "breq1.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "syl2an.mm"
include "r19.29.mm"
include "simplrr.mm"
include "simprl.mm"
include "adantr.mm"
include "max1.mm"
include "syl2anc.mm"
include "sselda.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "imim1d.mm"
include "impd.mm"
include "max2.mm"
include "adantld.mm"
include "eqid.mm"
include "limsupgf.mm"
include "ffvelrni.mm"
include "adantl.mm"
include "xrleid.mm"
include "adantrr.mm"
include "wf.mm"
include "limsupgle.mm"
include "syl211anc.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "syld.mm"
include "jcad.mm"
include "ad2antrr.mm"
include "ffvelrnda.mm"
include "xrletr.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "mpan2d.mm"
include "anassrs.mm"
include "ralrimdva.mm"
include "mpd.mm"
include "limsuple.mm"

theorem limsupbnd2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vm: setvar m
  let vn: setvar n
  assume limsupbnd.1: |- ( ph -> B C_ RR )
  assume limsupbnd.2: |- ( ph -> F : B --> RR* )
  assume limsupbnd.3: |- ( ph -> A e. RR* )
  assume limsupbnd2.4: |- ( ph -> sup ( B , RR* , < ) = +oo )
  assume limsupbnd2.5: |- ( ph -> E. k e. RR A. j e. B ( k <_ j -> A <_ ( F ` j ) ) )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  disjoint F j
  disjoint F k
  disjoint j ph
  disjoint k ph
  disjoint j m
  disjoint k m
  disjoint A m
  disjoint j n
  disjoint k n
  disjoint m n
  disjoint B m
  disjoint B n
  disjoint F m
  disjoint F n
  disjoint m ph
  assert |- ( ph -> A <_ ( limsup ` F ) )

  proof
    wph
    cA
    cF
    clsp
    cfv
    cle
    wbr
    #
    cA
    vm
    cv
    #
    vn
    cr
    cF
    vn
    cv
    #
    cpnf
    cico
    co
    cima
    cxr
    cin
    cxr
    clt
    csup
    cmpt
    #
    cfv
    #
    cle
    wbr
    #
    vm
    cr
    wral
    #
    wph
    vk
    cv
    #
    vj
    cv
    #
    cle
    wbr
    #
    cA
    @8
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vj
    cB
    wral
    #
    vk
    cr
    wrex
    #
    @6
    limsupbnd2.5
    wph
    @14
    @5
    vm
    cr
    wph
    @1
    cr
    wcel
    #
    wa
    #
    @13
    @5
    vk
    cr
    wph
    @15
    @7
    cr
    wcel
    #
    @13
    @5
    wi
    wph
    @15
    @17
    wa
    #
    wa
    #
    @13
    @7
    @1
    cle
    wbr
    #
    @1
    @7
    cif
    #
    @8
    cle
    wbr
    #
    vj
    cB
    wrex
    #
    @5
    wph
    @2
    @8
    cle
    wbr
    #
    vj
    cB
    wrex
    #
    vn
    cr
    wral
    #
    @21
    cr
    wcel
    #
    @23
    @18
    wph
    @26
    cB
    cxr
    clt
    csup
    cpnf
    wceq
    #
    limsupbnd2.4
    wph
    cB
    cxr
    wss
    @26
    @28
    wb
    wph
    cB
    cr
    cxr
    limsupbnd.1
    ressxr
    syl6ss
    vn
    vj
    cB
    supxrunb1
    syl
    mpbird
    @20
    @1
    @7
    cr
    ifcl
    #
    @25
    @23
    vn
    @21
    cr
    @2
    @21
    wceq
    @24
    @22
    vj
    cB
    @2
    @21
    @8
    cle
    breq1
    rexbidv
    rspccva
    syl2an
    @13
    @23
    wa
    @12
    @22
    wa
    #
    vj
    cB
    wrex
    @19
    @5
    @12
    @22
    vj
    cB
    r19.29
    @19
    @30
    @5
    vj
    cB
    @19
    @8
    cB
    wcel
    #
    wa
    #
    @30
    @11
    @10
    @4
    cle
    wbr
    #
    wa
    #
    @5
    @32
    @30
    @11
    @33
    @32
    @12
    @22
    @11
    @32
    @22
    @9
    @11
    @32
    @7
    @21
    cle
    wbr
    #
    @22
    @9
    @32
    @17
    @15
    @35
    wph
    @15
    @17
    @31
    simplrr
    #
    @19
    @15
    @31
    wph
    @15
    @17
    simprl
    #
    adantr
    #
    @7
    @1
    max1
    syl2anc
    @32
    @17
    @27
    @8
    cr
    wcel
    #
    @35
    @22
    wa
    @9
    wi
    @36
    @32
    @15
    @17
    @27
    @38
    @36
    @29
    syl2anc
    #
    @19
    cB
    cr
    @8
    wph
    cB
    cr
    wss
    #
    @18
    limsupbnd.1
    adantr
    #
    sselda
    #
    @7
    @21
    @8
    letr
    syl3anc
    mpand
    imim1d
    impd
    @32
    @30
    @1
    @8
    cle
    wbr
    #
    @33
    @32
    @22
    @44
    @12
    @32
    @1
    @21
    cle
    wbr
    #
    @22
    @44
    @32
    @17
    @15
    @45
    @36
    @38
    @7
    @1
    max2
    syl2anc
    @32
    @15
    @27
    @39
    @45
    @22
    wa
    @44
    wi
    @38
    @40
    @43
    @1
    @21
    @8
    letr
    syl3anc
    mpand
    adantld
    @19
    @44
    @33
    wi
    #
    vj
    cB
    @19
    @4
    @4
    cle
    wbr
    #
    @46
    vj
    cB
    wral
    #
    wph
    @15
    @47
    @17
    @16
    @4
    cxr
    wcel
    #
    @47
    @15
    @49
    wph
    cr
    cxr
    @1
    @3
    vn
    cF
    @3
    @3
    eqid
    #
    limsupgf
    ffvelrni
    #
    adantl
    @4
    xrleid
    syl
    adantrr
    @19
    @41
    cB
    cxr
    cF
    wf
    #
    @15
    @49
    @47
    @48
    wb
    @42
    wph
    @52
    @18
    limsupbnd.2
    adantr
    #
    @37
    @19
    @15
    @49
    @37
    @51
    syl
    #
    @4
    cB
    @1
    vj
    vn
    cF
    @3
    @50
    limsupgle
    syl211anc
    mpbid
    r19.21bi
    syld
    jcad
    @32
    cA
    cxr
    wcel
    #
    @10
    cxr
    wcel
    @49
    @34
    @5
    wi
    wph
    @55
    @18
    @31
    limsupbnd.3
    ad2antrr
    @19
    cB
    cxr
    @8
    cF
    @53
    ffvelrnda
    @19
    @49
    @31
    @54
    adantr
    cA
    @10
    @4
    xrletr
    syl3anc
    syld
    rexlimdva
    syl5
    mpan2d
    anassrs
    rexlimdva
    ralrimdva
    mpd
    wph
    @41
    @52
    @55
    @0
    @6
    wb
    limsupbnd.1
    limsupbnd.2
    limsupbnd.3
    cA
    cB
    vm
    vn
    cF
    @3
    @50
    limsuple
    syl3anc
    mpbird
end
