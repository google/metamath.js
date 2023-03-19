include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "cmbf.mm"
include "cr.mm"
include "cv.mm"
include "cc0.mm"
include "ci.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "citg2.mm"
include "c3.mm"
include "cfz.mm"
include "wral.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfss.mm"
include "wceq.mm"
include "wss.mm"
include "adantr.mm"
include "sselda.mm"
include "iftrued.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "ifid.mm"
include "cdif.mm"
include "simplll.mm"
include "simpr.mm"
include "simplr.mm"
include "eldifd.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "cz.mm"
include "simpllr.mm"
include "elfzelz.mm"
include "cc.mm"
include "wne.mm"
include "ax-icn.mm"
include "ine0.mm"
include "w3a.mm"
include "expclz.mm"
include "expne0i.mm"
include "div0d.mm"
include "mp3an12.mm"
include "3syl.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "re0.mm"
include "syl6eq.mm"
include "ifeq1d.mm"
include "ifeq1da.mm"
include "iffalse.mm"
include "3eqtr4a.mm"
include "pm2.61dan.mm"
include "ifan.mm"
include "3eqtr4g.mm"
include "mpteq2dv.mm"
include "eqidd.mm"
include "iblitg.mm"
include "sylan2.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "wo.mm"
include "cun.mm"
include "elun.mm"
include "undif2.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "biimpar.mm"
include "mbfmptcl.mm"
include "0cn.mm"
include "syl6eqel.mm"
include "jaodan.mm"
include "syldan.mm"
include "isibl2.mm"
include "mpbir2and.mm"

theorem iblss2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vk: setvar k
  assume iblss2.1: |- ( ph -> A C_ B )
  assume iblss2.2: |- ( ph -> B e. dom vol )
  assume iblss2.3: |- ( ( ph /\ x e. A ) -> C e. V )
  assume iblss2.4: |- ( ( ph /\ x e. ( B \ A ) ) -> C = 0 )
  assume iblss2.5: |- ( ph -> ( x e. A |-> C ) e. L^1 )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint V x
  disjoint k x
  disjoint B k
  disjoint C k
  disjoint k ph
  assert |- ( ph -> ( x e. B |-> C ) e. L^1 )

  proof
    wph
    vx
    cB
    cC
    cmpt
    #
    cibl
    wcel
    @0
    cmbf
    wcel
    vx
    cr
    vx
    cv
    #
    cB
    wcel
    #
    cc0
    cC
    ci
    vk
    cv
    #
    cexp
    co
    #
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
    cr
    wcel
    #
    vk
    cc0
    c3
    cfz
    co
    #
    wral
    wph
    vx
    cA
    cB
    cC
    cV
    iblss2.1
    iblss2.2
    iblss2.3
    iblss2.4
    wph
    vx
    cA
    cC
    cmpt
    #
    cibl
    wcel
    @13
    cmbf
    wcel
    iblss2.5
    @13
    iblmbf
    syl
    #
    mbfss
    wph
    @11
    vk
    @12
    wph
    @3
    @12
    wcel
    #
    wa
    #
    @10
    vx
    cr
    @1
    cA
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
    cr
    @16
    @9
    @19
    citg2
    @16
    vx
    cr
    @8
    @18
    @16
    @2
    @7
    @6
    cc0
    cif
    #
    cc0
    cif
    #
    @17
    @21
    cc0
    cif
    #
    @8
    @18
    @16
    @17
    @22
    @23
    wceq
    @16
    @17
    wa
    #
    @22
    @21
    @23
    @24
    @2
    @21
    cc0
    @16
    cA
    cB
    @1
    wph
    cA
    cB
    wss
    #
    @15
    iblss2.1
    adantr
    sselda
    iftrued
    @17
    @23
    @21
    wceq
    @16
    @17
    @21
    cc0
    iftrue
    adantl
    eqtr4d
    @16
    @17
    wn
    #
    wa
    #
    @2
    cc0
    cc0
    cif
    cc0
    @22
    @23
    @2
    cc0
    ifid
    @27
    @2
    @21
    cc0
    cc0
    @27
    @2
    wa
    #
    @21
    @7
    cc0
    cc0
    cif
    cc0
    @28
    @7
    @6
    cc0
    cc0
    @28
    @6
    cc0
    cre
    cfv
    cc0
    @28
    @5
    cc0
    cre
    @28
    @5
    cc0
    @4
    cdiv
    co
    #
    cc0
    @28
    cC
    cc0
    @4
    cdiv
    @28
    wph
    @1
    cB
    cA
    cdif
    #
    wcel
    #
    cC
    cc0
    wceq
    wph
    @15
    @26
    @2
    simplll
    @28
    @1
    cB
    cA
    @27
    @2
    simpr
    @16
    @26
    @2
    simplr
    eldifd
    iblss2.4
    syl2anc
    oveq1d
    @28
    @15
    @3
    cz
    wcel
    #
    @29
    cc0
    wceq
    #
    wph
    @15
    @26
    @2
    simpllr
    @3
    cc0
    c3
    elfzelz
    #
    ci
    cc
    wcel
    #
    ci
    cc0
    wne
    #
    @32
    @33
    ax-icn
    ine0
    @35
    @36
    @32
    w3a
    @4
    ci
    @3
    expclz
    ci
    @3
    expne0i
    div0d
    mp3an12
    3syl
    eqtrd
    fveq2d
    re0
    syl6eq
    ifeq1d
    @7
    cc0
    ifid
    syl6eq
    ifeq1da
    @26
    @23
    cc0
    wceq
    @16
    @17
    @21
    cc0
    iffalse
    adantl
    3eqtr4a
    pm2.61dan
    @2
    @7
    @6
    cc0
    ifan
    @17
    @7
    @6
    cc0
    ifan
    3eqtr4g
    mpteq2dv
    fveq2d
    @15
    wph
    @32
    @20
    cr
    wcel
    @34
    wph
    vx
    cA
    cC
    @6
    @19
    @3
    cV
    wph
    @19
    eqidd
    wph
    @17
    wa
    @6
    eqidd
    iblss2.5
    iblss2.3
    iblitg
    sylan2
    eqeltrd
    ralrimiva
    wph
    vx
    cB
    cC
    @6
    vk
    @9
    cc
    wph
    @9
    eqidd
    wph
    @2
    wa
    @6
    eqidd
    wph
    @2
    @17
    @31
    wo
    #
    cC
    cc
    wcel
    #
    wph
    @37
    @2
    @37
    @1
    cA
    @30
    cun
    #
    wcel
    wph
    @2
    @1
    cA
    @30
    elun
    wph
    @39
    cB
    @1
    wph
    @39
    cA
    cB
    cun
    #
    cB
    cA
    cB
    undif2
    wph
    @25
    @40
    cB
    wceq
    iblss2.1
    cA
    cB
    ssequn1
    sylib
    syl5eq
    eleq2d
    syl5bbr
    biimpar
    wph
    @17
    @38
    @31
    wph
    vx
    cA
    cC
    cV
    @14
    iblss2.3
    mbfmptcl
    wph
    @31
    wa
    cC
    cc0
    cc
    iblss2.4
    0cn
    syl6eqel
    jaodan
    syldan
    isibl2
    mpbir2and
end
