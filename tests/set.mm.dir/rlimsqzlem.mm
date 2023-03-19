include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "cv.mm"
include "cle.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cpnf.mm"
include "cico.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "ad3antrrr.mm"
include "wb.mm"
include "ad2antrr.mm"
include "elicopnf.mm"
include "syl.mm"
include "simprbda.mm"
include "adantrr.mm"
include "wss.mm"
include "cdm.mm"
include "cc.mm"
include "eqid.mm"
include "dmmptd.mm"
include "rlimss.mm"
include "eqsstr3d.mm"
include "adantr.mm"
include "sselda.mm"
include "simplbda.mm"
include "simprr.mm"
include "letrd.mm"
include "anassrs.mm"
include "adantllr.mm"
include "syldan.mm"
include "subcld.mm"
include "abscld.mm"
include "adantlr.mm"
include "rlimcl.mm"
include "rpre.mm"
include "ad3antlr.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "expr.mm"
include "an32s.mm"
include "a2d.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "ralrimiva.mm"
include "rlim3.mm"
include "3imtr4d.mm"
include "mpd.mm"

theorem rlimsqzlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cM: class M
  let vy: setvar y
  let vz: setvar z
  assume rlimsqzlem.m: |- ( ph -> M e. RR )
  assume rlimsqzlem.e: |- ( ph -> E e. CC )
  assume rlimsqzlem.1: |- ( ph -> ( x e. A |-> B ) ~~>r D )
  assume rlimsqzlem.2: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume rlimsqzlem.3: |- ( ( ph /\ x e. A ) -> C e. CC )
  assume rlimsqzlem.4: |- ( ( ph /\ ( x e. A /\ M <_ x ) ) -> ( abs ` ( C - E ) ) <_ ( abs ` ( B - D ) ) )

  disjoint A x
  disjoint D x
  disjoint E x
  disjoint ph x
  disjoint M x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint D y
  disjoint D z
  disjoint E y
  disjoint E z
  disjoint ph y
  disjoint ph z
  disjoint C y
  disjoint C z
  disjoint M z
  assert |- ( ph -> ( x e. A |-> C ) ~~>r E )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cD
    crli
    wbr
    #
    vx
    cA
    cC
    cmpt
    cE
    crli
    wbr
    #
    rlimsqzlem.1
    wph
    vz
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    cB
    cD
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vz
    cM
    cpnf
    cico
    co
    #
    wrex
    #
    vy
    crp
    wral
    @5
    cC
    cE
    cmin
    co
    #
    cabs
    cfv
    #
    @8
    clt
    wbr
    #
    wi
    #
    vx
    cA
    wral
    #
    vz
    @12
    wrex
    #
    vy
    crp
    wral
    @1
    @2
    wph
    @13
    @19
    vy
    crp
    wph
    @8
    crp
    wcel
    #
    wa
    #
    @11
    @18
    vz
    @12
    @21
    @3
    @12
    wcel
    #
    wa
    #
    @10
    @17
    vx
    cA
    @23
    @4
    cA
    wcel
    #
    wa
    @5
    @9
    @16
    @21
    @24
    @22
    @5
    @9
    @16
    wi
    #
    wi
    @21
    @24
    wa
    #
    @22
    @5
    @25
    @26
    @22
    @5
    wa
    #
    wa
    #
    @15
    @7
    cle
    wbr
    #
    @9
    @16
    @26
    @27
    cM
    @4
    cle
    wbr
    #
    @29
    @28
    cM
    @3
    @4
    wph
    cM
    cr
    wcel
    #
    @20
    @24
    @27
    rlimsqzlem.m
    ad3antrrr
    @26
    @22
    @3
    cr
    wcel
    #
    @5
    @26
    @22
    @32
    cM
    @3
    cle
    wbr
    #
    @26
    @31
    @22
    @32
    @33
    wa
    wb
    wph
    @31
    @20
    @24
    rlimsqzlem.m
    ad2antrr
    cM
    @3
    elicopnf
    syl
    #
    simprbda
    adantrr
    @26
    @4
    cr
    wcel
    @27
    @21
    cA
    cr
    @4
    wph
    cA
    cr
    wss
    @20
    wph
    cA
    @0
    cdm
    #
    cr
    wph
    vx
    @0
    cA
    cB
    cc
    @0
    eqid
    rlimsqzlem.2
    dmmptd
    wph
    @1
    @35
    cr
    wss
    rlimsqzlem.1
    cD
    @0
    rlimss
    syl
    eqsstr3d
    #
    adantr
    sselda
    adantr
    @26
    @22
    @33
    @5
    @26
    @22
    @32
    @33
    @34
    simplbda
    adantrr
    @26
    @22
    @5
    simprr
    letrd
    wph
    @24
    @30
    @29
    @20
    wph
    @24
    @30
    @29
    rlimsqzlem.4
    anassrs
    adantllr
    syldan
    @28
    @15
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @29
    @9
    wa
    @16
    wi
    @26
    @37
    @27
    wph
    @24
    @37
    @20
    wph
    @24
    wa
    #
    @14
    @40
    cC
    cE
    rlimsqzlem.3
    wph
    cE
    cc
    wcel
    @24
    rlimsqzlem.e
    adantr
    subcld
    abscld
    adantlr
    adantr
    @26
    @38
    @27
    wph
    @24
    @38
    @20
    @40
    @6
    @40
    cB
    cD
    rlimsqzlem.2
    wph
    cD
    cc
    wcel
    #
    @24
    wph
    @1
    @41
    rlimsqzlem.1
    cD
    @0
    rlimcl
    syl
    #
    adantr
    subcld
    abscld
    adantlr
    adantr
    @20
    @39
    wph
    @24
    @27
    @8
    rpre
    ad3antlr
    @15
    @7
    @8
    lelttr
    syl3anc
    mpand
    expr
    an32s
    a2d
    ralimdva
    reximdva
    ralimdva
    wph
    vy
    vz
    vx
    cA
    cB
    cD
    cM
    wph
    cB
    cc
    wcel
    vx
    cA
    rlimsqzlem.2
    ralrimiva
    @36
    @42
    rlimsqzlem.m
    rlim3
    wph
    vy
    vz
    vx
    cA
    cC
    cE
    cM
    wph
    cC
    cc
    wcel
    vx
    cA
    rlimsqzlem.3
    ralrimiva
    @36
    rlimsqzlem.e
    rlimsqzlem.m
    rlim3
    3imtr4d
    mpd
end
