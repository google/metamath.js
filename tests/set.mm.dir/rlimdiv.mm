include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cmpt.mm"
include "crli.mm"
include "cc.mm"
include "rlimmptrcl.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "reccld.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "ccom.mm"
include "cfv.mm"
include "wne.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "fmptd.mm"
include "wbr.mm"
include "rlimcl.mm"
include "syl.mm"
include "reccl.mm"
include "sylbi.mm"
include "adantl.mm"
include "crp.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cle.mm"
include "cif.mm"
include "c2.mm"
include "reccn2.mm"
include "sylan.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "wceq.mm"
include "oveqan12rd.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "biimpar.mm"
include "syldan.mm"
include "rlimcn1.mm"
include "eqidd.mm"
include "fmptco.mm"
include "3brtr3d.mm"
include "rlimmul.mm"
include "divrecd.mm"
include "mpteq2dva.mm"
include "3brtr4d.mm"

theorem rlimdiv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  assume rlimadd.3: |- ( ( ph /\ x e. A ) -> B e. V )
  assume rlimadd.4: |- ( ( ph /\ x e. A ) -> C e. V )
  assume rlimadd.5: |- ( ph -> ( x e. A |-> B ) ~~>r D )
  assume rlimadd.6: |- ( ph -> ( x e. A |-> C ) ~~>r E )
  assume rlimdiv.7: |- ( ph -> E =/= 0 )
  assume rlimdiv.8: |- ( ( ph /\ x e. A ) -> C =/= 0 )

  disjoint A x
  disjoint D x
  disjoint ph x
  disjoint E x
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E y
  disjoint E z
  assert |- ( ph -> ( x e. A |-> ( B / C ) ) ~~>r ( D / E ) )

  proof
    wph
    vx
    cA
    cB
    c1
    cC
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    cD
    c1
    cE
    cdiv
    co
    #
    cmul
    co
    vx
    cA
    cB
    cC
    cdiv
    co
    #
    cmpt
    cD
    cE
    cdiv
    co
    crli
    wph
    vx
    cA
    cB
    @0
    cD
    @2
    cc
    wph
    cA
    cB
    cD
    vx
    cV
    rlimadd.3
    rlimadd.5
    rlimmptrcl
    #
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cC
    wph
    cA
    cC
    cE
    vx
    cV
    rlimadd.4
    rlimadd.6
    rlimmptrcl
    #
    rlimdiv.8
    reccld
    rlimadd.5
    wph
    vy
    cc
    cc0
    csn
    cdif
    #
    c1
    vy
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    vx
    cA
    cC
    cmpt
    #
    ccom
    cE
    @10
    cfv
    #
    vx
    cA
    @0
    cmpt
    @2
    crli
    wph
    vz
    vw
    vv
    cA
    cE
    @10
    @11
    @7
    wph
    vx
    cA
    cC
    @7
    @11
    @5
    cC
    cc
    wcel
    cC
    cc0
    wne
    cC
    @7
    wcel
    @6
    rlimdiv.8
    cC
    cc
    cc0
    eldifsn
    sylanbrc
    #
    @11
    eqid
    fmptd
    wph
    cE
    cc
    wcel
    #
    cE
    cc0
    wne
    cE
    @7
    wcel
    #
    wph
    @11
    cE
    crli
    wbr
    @14
    rlimadd.6
    cE
    @11
    rlimcl
    syl
    #
    rlimdiv.7
    cE
    cc
    cc0
    eldifsn
    sylanbrc
    #
    rlimadd.6
    wph
    vy
    @7
    @9
    cc
    @10
    @8
    @7
    wcel
    #
    @9
    cc
    wcel
    #
    wph
    @18
    @8
    cc
    wcel
    @8
    cc0
    wne
    wa
    @19
    @8
    cc
    cc0
    eldifsn
    @8
    reccl
    sylbi
    adantl
    @10
    eqid
    #
    fmptd
    wph
    vz
    cv
    #
    crp
    wcel
    #
    vv
    cv
    #
    cE
    cmin
    co
    cabs
    cfv
    vw
    cv
    clt
    wbr
    #
    c1
    @23
    cdiv
    co
    #
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    @21
    clt
    wbr
    #
    wi
    #
    vv
    @7
    wral
    #
    vw
    crp
    wrex
    #
    @24
    @23
    @10
    cfv
    #
    @12
    cmin
    co
    #
    cabs
    cfv
    #
    @21
    clt
    wbr
    #
    wi
    #
    vv
    @7
    wral
    #
    vw
    crp
    wrex
    #
    wph
    @15
    @22
    @31
    @17
    vw
    vv
    cE
    @21
    c1
    cE
    cabs
    cfv
    #
    @21
    cmul
    co
    #
    cle
    wbr
    c1
    @40
    cif
    @39
    c2
    cdiv
    co
    cmul
    co
    #
    @41
    eqid
    reccn2
    sylan
    wph
    @38
    @31
    wph
    @37
    @30
    vw
    crp
    wph
    @36
    @29
    vv
    @7
    wph
    @23
    @7
    wcel
    #
    wa
    #
    @35
    @28
    @24
    @43
    @34
    @27
    @21
    clt
    @43
    @33
    @26
    cabs
    @42
    wph
    @32
    @25
    @12
    @2
    cmin
    vy
    @23
    @9
    @25
    @7
    @10
    @8
    @23
    c1
    cdiv
    oveq2
    @20
    c1
    @23
    cdiv
    ovex
    fvmpt
    wph
    @15
    @12
    @2
    wceq
    @17
    vy
    cE
    @9
    @2
    @7
    @10
    @8
    cE
    c1
    cdiv
    oveq2
    @20
    c1
    cE
    cdiv
    ovex
    fvmpt
    syl
    #
    oveqan12rd
    fveq2d
    breq1d
    imbi2d
    ralbidva
    rexbidv
    biimpar
    syldan
    rlimcn1
    wph
    vx
    vy
    cA
    @7
    cC
    @9
    @0
    @11
    @10
    @13
    wph
    @11
    eqidd
    wph
    @10
    eqidd
    @8
    cC
    c1
    cdiv
    oveq2
    fmptco
    @44
    3brtr3d
    rlimmul
    wph
    vx
    cA
    @3
    @1
    @5
    cB
    cC
    @4
    @6
    rlimdiv.8
    divrecd
    mpteq2dva
    wph
    cD
    cE
    wph
    vx
    cA
    cB
    cmpt
    #
    cD
    crli
    wbr
    cD
    cc
    wcel
    rlimadd.5
    cD
    @45
    rlimcl
    syl
    @16
    rlimdiv.7
    divrecd
    3brtr4d
end
