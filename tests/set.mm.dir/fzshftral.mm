include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "cc0.mm"
include "cv.mm"
include "cmin.mm"
include "wsbc.mm"
include "caddc.mm"
include "wb.mm"
include "0z.mm"
include "fzrevral.mm"
include "mp3an3.mm"
include "3adant3.mm"
include "zsubcl.mm"
include "mpan.mm"
include "id.mm"
include "syl3an.mm"
include "3com12.mm"
include "cvv.mm"
include "ovex.mm"
include "oveq2.mm"
include "sbcco3g.mm"
include "ax-mp.mm"
include "ralbii.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "wa.mm"
include "cneg.mm"
include "df-neg.mm"
include "oveq2i.mm"
include "subneg.mm"
include "addcom.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "3coml.mm"
include "raleqdv.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "negsubdi2.mm"
include "syl2an.mm"
include "sbceq1d.mm"
include "ralbidva.mm"
include "3ad2ant3.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "3bitrd.mm"

theorem fzshftral
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x

  disjoint j k
  disjoint K j
  disjoint K k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint k ph
  disjoint j x
  disjoint k x
  disjoint K x
  disjoint M x
  disjoint N x
  disjoint ph x
  assert |- ( ( M e. ZZ /\ N e. ZZ /\ K e. ZZ ) -> ( A. j e. ( M ... N ) ph <-> A. k e. ( ( M + K ) ... ( N + K ) ) [. ( k - K ) / j ]. ph ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    w3a
    #
    wph
    vj
    cM
    cN
    cfz
    co
    wral
    #
    wph
    vj
    cc0
    vx
    cv
    #
    cmin
    co
    #
    wsbc
    #
    vx
    cc0
    cN
    cmin
    co
    #
    cc0
    cM
    cmin
    co
    #
    cfz
    co
    wral
    #
    @7
    vx
    cK
    vk
    cv
    #
    cmin
    co
    #
    wsbc
    #
    vk
    cK
    @9
    cmin
    co
    #
    cK
    @8
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wph
    vj
    @11
    cK
    cmin
    co
    #
    wsbc
    #
    vk
    cM
    cK
    caddc
    co
    #
    cN
    cK
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    @0
    @1
    @4
    @10
    wb
    #
    @2
    @0
    @1
    cc0
    cz
    wcel
    #
    @24
    0z
    wph
    vj
    vx
    cc0
    cM
    cN
    fzrevral
    mp3an3
    3adant3
    @1
    @0
    @2
    @10
    @17
    wb
    #
    @1
    @8
    cz
    wcel
    #
    @0
    @9
    cz
    wcel
    #
    @2
    @2
    @26
    @25
    @1
    @27
    0z
    cc0
    cN
    zsubcl
    mpan
    @25
    @0
    @28
    0z
    cc0
    cM
    zsubcl
    mpan
    @2
    id
    @7
    vx
    vk
    cK
    @8
    @9
    fzrevral
    syl3an
    3com12
    @17
    wph
    vj
    cc0
    @12
    cmin
    co
    #
    wsbc
    #
    vk
    @16
    wral
    #
    @3
    @23
    @13
    @30
    vk
    @16
    @12
    cvv
    wcel
    @13
    @30
    wb
    cK
    @11
    cmin
    ovex
    wph
    vx
    vj
    @12
    @6
    @29
    cvv
    @5
    @12
    cc0
    cmin
    oveq2
    sbcco3g
    ax-mp
    ralbii
    @3
    @31
    @30
    vk
    @22
    wral
    #
    @23
    @3
    @30
    vk
    @16
    @22
    @0
    cM
    cc
    wcel
    #
    @1
    cN
    cc
    wcel
    #
    @2
    cK
    cc
    wcel
    #
    @16
    @22
    wceq
    #
    cM
    zcn
    cN
    zcn
    cK
    zcn
    #
    @35
    @33
    @34
    @36
    @35
    @33
    @34
    w3a
    @14
    @20
    @15
    @21
    cfz
    @35
    @33
    @14
    @20
    wceq
    @34
    @35
    @33
    wa
    #
    @14
    cK
    cM
    cneg
    #
    cmin
    co
    #
    @20
    @39
    @9
    cK
    cmin
    cM
    df-neg
    oveq2i
    @38
    @40
    cK
    cM
    caddc
    co
    @20
    cK
    cM
    subneg
    cK
    cM
    addcom
    eqtrd
    syl5eqr
    3adant3
    @35
    @34
    @15
    @21
    wceq
    @33
    @35
    @34
    wa
    #
    @15
    cK
    cN
    cneg
    #
    cmin
    co
    #
    @21
    @42
    @8
    cK
    cmin
    cN
    df-neg
    oveq2i
    @41
    @43
    cK
    cN
    caddc
    co
    @21
    cK
    cN
    subneg
    cK
    cN
    addcom
    eqtrd
    syl5eqr
    3adant2
    oveq12d
    3coml
    syl3an
    raleqdv
    @2
    @0
    @32
    @23
    wb
    @1
    @2
    @30
    @19
    vk
    @22
    @2
    @11
    @22
    wcel
    #
    wa
    wph
    vj
    @29
    @18
    @2
    @35
    @11
    cc
    wcel
    #
    @29
    @18
    wceq
    @44
    @37
    @44
    @11
    @11
    @20
    @21
    elfzelz
    zcnd
    @35
    @45
    wa
    @29
    @12
    cneg
    @18
    @12
    df-neg
    cK
    @11
    negsubdi2
    syl5eqr
    syl2an
    sbceq1d
    ralbidva
    3ad2ant3
    bitrd
    syl5bb
    3bitrd
end
