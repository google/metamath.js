include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cr.mm"
include "wcel.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cmul.mm"
include "csu.mm"
include "citg.mm"
include "cz.mm"
include "wceq.mm"
include "elfzelz.mm"
include "wn.mm"
include "iffalse.mm"
include "ad2antll.mm"
include "cdif.mm"
include "eldif.mm"
include "adantlr.mm"
include "oveq1d.mm"
include "cc.mm"
include "wne.mm"
include "ax-icn.mm"
include "ine0.mm"
include "expclz.mm"
include "mp3an12.mm"
include "expne0i.mm"
include "div0d.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "re0.mm"
include "syl6eq.mm"
include "ifeq1d.mm"
include "ifid.mm"
include "sylan2br.mm"
include "eqtr4d.mm"
include "expr.mm"
include "iftrue.mm"
include "pm2.61d2.mm"
include "adantl.mm"
include "wss.mm"
include "adantr.mm"
include "sseld.mm"
include "con3dimp.mm"
include "syl.mm"
include "pm2.61dan.mm"
include "ifan.mm"
include "3eqtr4g.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "sylan2.mm"
include "sumeq2dv.mm"
include "eqid.mm"
include "dfitg.mm"

theorem itgss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume itgss.1: |- ( ph -> A C_ B )
  assume itgss.2: |- ( ( ph /\ x e. ( B \ A ) ) -> C = 0 )

  disjoint ph x
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint k x
  disjoint k ph
  assert |- ( ph -> S. A C _d x = S. B C _d x )

  proof
    wph
    cc0
    c3
    cfz
    co
    #
    ci
    vk
    cv
    #
    cexp
    co
    #
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    cc0
    cC
    @2
    cdiv
    co
    #
    cre
    cfv
    #
    cle
    wbr
    #
    wa
    @6
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    @0
    @2
    vx
    cr
    @3
    cB
    wcel
    #
    @7
    wa
    @6
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    cmul
    co
    #
    vk
    csu
    vx
    cA
    cC
    citg
    vx
    cB
    cC
    citg
    wph
    @0
    @11
    @16
    vk
    @1
    @0
    wcel
    wph
    @1
    cz
    wcel
    #
    @11
    @16
    wceq
    @1
    cc0
    c3
    elfzelz
    wph
    @17
    wa
    #
    @10
    @15
    @2
    cmul
    @18
    @9
    @14
    citg2
    @18
    vx
    cr
    @8
    @13
    @18
    @4
    @7
    @6
    cc0
    cif
    #
    cc0
    cif
    #
    @12
    @19
    cc0
    cif
    #
    @8
    @13
    @18
    @12
    @20
    @21
    wceq
    @18
    @12
    wa
    #
    @20
    @19
    @21
    @22
    @4
    @20
    @19
    wceq
    #
    @18
    @12
    @4
    wn
    #
    @23
    @18
    @12
    @24
    wa
    #
    wa
    @20
    cc0
    @19
    @24
    @20
    cc0
    wceq
    #
    @18
    @12
    @4
    @19
    cc0
    iffalse
    #
    ad2antll
    @25
    @18
    @3
    cB
    cA
    cdif
    wcel
    #
    @19
    cc0
    wceq
    @3
    cB
    cA
    eldif
    @18
    @28
    wa
    #
    @19
    @7
    cc0
    cc0
    cif
    cc0
    @29
    @7
    @6
    cc0
    cc0
    @29
    @6
    cc0
    cre
    cfv
    cc0
    @29
    @5
    cc0
    cre
    @29
    @5
    cc0
    @2
    cdiv
    co
    #
    cc0
    @29
    cC
    cc0
    @2
    cdiv
    wph
    @28
    cC
    cc0
    wceq
    @17
    itgss.2
    adantlr
    oveq1d
    @17
    @30
    cc0
    wceq
    wph
    @28
    @17
    @2
    ci
    cc
    wcel
    #
    ci
    cc0
    wne
    #
    @17
    @2
    cc
    wcel
    ax-icn
    ine0
    ci
    @1
    expclz
    mp3an12
    @31
    @32
    @17
    @2
    cc0
    wne
    ax-icn
    ine0
    ci
    @1
    expne0i
    mp3an12
    div0d
    ad2antlr
    eqtrd
    fveq2d
    re0
    syl6eq
    ifeq1d
    @7
    cc0
    ifid
    syl6eq
    sylan2br
    eqtr4d
    expr
    @4
    @19
    cc0
    iftrue
    pm2.61d2
    @12
    @21
    @19
    wceq
    @18
    @12
    @19
    cc0
    iftrue
    adantl
    eqtr4d
    @18
    @12
    wn
    #
    wa
    #
    @20
    cc0
    @21
    @34
    @24
    @26
    @18
    @4
    @12
    @18
    cA
    cB
    @3
    wph
    cA
    cB
    wss
    @17
    itgss.1
    adantr
    sseld
    con3dimp
    @27
    syl
    @33
    @21
    cc0
    wceq
    @18
    @12
    @19
    cc0
    iffalse
    adantl
    eqtr4d
    pm2.61dan
    @4
    @7
    @6
    cc0
    ifan
    @12
    @7
    @6
    cc0
    ifan
    3eqtr4g
    mpteq2dv
    fveq2d
    oveq2d
    sylan2
    sumeq2dv
    vx
    cA
    cC
    @6
    vk
    @6
    eqid
    #
    dfitg
    vx
    cB
    cC
    @6
    vk
    @35
    dfitg
    3eqtr4g
end
