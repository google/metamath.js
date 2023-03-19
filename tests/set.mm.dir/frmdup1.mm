include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "c0.mm"
include "c0g.mm"
include "w3a.mm"
include "cmhm.mm"
include "frmdmnd.mm"
include "syl.mm"
include "jca.mm"
include "cword.mm"
include "ccom.mm"
include "cgsu.mm"
include "adantr.mm"
include "simpr.mm"
include "wrdco.mm"
include "syl2anc.mm"
include "gsumwcl.mm"
include "fmptd.mm"
include "eqid.mm"
include "frmdbas.mm"
include "feq2d.mm"
include "mpbird.mm"
include "cconcat.mm"
include "frmdelbas.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "ccatco.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "gsumccat.mm"
include "eqtrd.mm"
include "frmdadd.mm"
include "adantl.mm"
include "fveq2d.mm"
include "ccatcl.mm"
include "coeq2.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "wrd0.mm"
include "co02.mm"
include "syl6eq.mm"
include "gsum0.mm"
include "mp1i.mm"
include "3jca.mm"
include "frmd0.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem frmdup1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cE: class E
  let cG: class G
  let cI: class I
  let cM: class M
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cY: class Y
  assume frmdup.m: |- M = ( freeMnd ` I )
  assume frmdup.b: |- B = ( Base ` G )
  assume frmdup.e: |- E = ( x e. Word I |-> ( G gsum ( A o. x ) ) )
  assume frmdup.g: |- ( ph -> G e. Mnd )
  assume frmdup.i: |- ( ph -> I e. X )
  assume frmdup.a: |- ( ph -> A : I --> B )

  disjoint A x
  disjoint B x
  disjoint G x
  disjoint ph x
  disjoint I x
  disjoint y z
  disjoint E y
  disjoint E z
  disjoint x y
  disjoint x z
  disjoint G y
  disjoint G z
  disjoint ph y
  disjoint ph z
  disjoint Y x
  disjoint I y
  disjoint I z
  disjoint M y
  disjoint M z
  assert |- ( ph -> E e. ( M MndHom G ) )

  proof
    wph
    cM
    cmnd
    wcel
    #
    cG
    cmnd
    wcel
    #
    wa
    cM
    cbs
    cfv
    #
    cB
    cE
    wf
    #
    vy
    cv
    #
    vz
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    cE
    cfv
    #
    @4
    cE
    cfv
    #
    @5
    cE
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vz
    @2
    wral
    vy
    @2
    wral
    #
    c0
    cE
    cfv
    cG
    c0g
    cfv
    #
    wceq
    #
    w3a
    cE
    cM
    cG
    cmhm
    co
    wcel
    wph
    @0
    @1
    wph
    cI
    cX
    wcel
    #
    @0
    frmdup.i
    cI
    cM
    cX
    frmdup.m
    frmdmnd
    syl
    frmdup.g
    jca
    wph
    @3
    @14
    @16
    wph
    @3
    cI
    cword
    #
    cB
    cE
    wf
    wph
    vx
    @18
    cG
    cA
    vx
    cv
    #
    ccom
    #
    cgsu
    co
    #
    cB
    cE
    wph
    @19
    @18
    wcel
    #
    wa
    #
    @1
    @20
    cB
    cword
    #
    wcel
    #
    @21
    cB
    wcel
    wph
    @1
    @22
    frmdup.g
    adantr
    @23
    @22
    cI
    cB
    cA
    wf
    #
    @25
    wph
    @22
    simpr
    wph
    @26
    @22
    frmdup.a
    adantr
    cI
    cB
    cA
    @19
    wrdco
    syl2anc
    cB
    cG
    @20
    frmdup.b
    gsumwcl
    syl2anc
    frmdup.e
    fmptd
    wph
    @2
    @18
    cB
    cE
    wph
    @17
    @2
    @18
    wceq
    frmdup.i
    @2
    cI
    cM
    cX
    frmdup.m
    @2
    eqid
    #
    frmdbas
    syl
    feq2d
    mpbird
    wph
    @13
    vy
    vz
    @2
    @2
    wph
    @4
    @2
    wcel
    #
    @5
    @2
    wcel
    #
    wa
    #
    wa
    #
    cG
    cA
    @4
    @5
    cconcat
    co
    #
    ccom
    #
    cgsu
    co
    #
    cG
    cA
    @4
    ccom
    #
    cgsu
    co
    #
    cG
    cA
    @5
    ccom
    #
    cgsu
    co
    #
    @11
    co
    #
    @8
    @12
    @31
    @34
    cG
    @35
    @37
    cconcat
    co
    #
    cgsu
    co
    #
    @39
    @31
    @33
    @40
    cG
    cgsu
    @31
    @4
    @18
    wcel
    #
    @5
    @18
    wcel
    #
    @26
    @33
    @40
    wceq
    @28
    @42
    wph
    @29
    @2
    cI
    cM
    @4
    frmdup.m
    @27
    frmdelbas
    ad2antrl
    #
    @29
    @43
    wph
    @28
    @2
    cI
    cM
    @5
    frmdup.m
    @27
    frmdelbas
    ad2antll
    #
    wph
    @26
    @30
    frmdup.a
    adantr
    #
    cI
    cB
    @4
    @5
    cA
    ccatco
    syl3anc
    oveq2d
    @31
    @1
    @35
    @24
    wcel
    #
    @37
    @24
    wcel
    #
    @41
    @39
    wceq
    wph
    @1
    @30
    frmdup.g
    adantr
    @31
    @42
    @26
    @47
    @44
    @46
    cI
    cB
    cA
    @4
    wrdco
    syl2anc
    @31
    @43
    @26
    @48
    @45
    @46
    cI
    cB
    cA
    @5
    wrdco
    syl2anc
    cB
    @11
    cG
    @35
    @37
    frmdup.b
    @11
    eqid
    #
    gsumccat
    syl3anc
    eqtrd
    @31
    @8
    @32
    cE
    cfv
    #
    @34
    @31
    @7
    @32
    cE
    @30
    @7
    @32
    wceq
    wph
    @2
    @6
    cI
    cM
    @4
    @5
    frmdup.m
    @27
    @6
    eqid
    #
    frmdadd
    adantl
    fveq2d
    @31
    @32
    @18
    wcel
    #
    @50
    @34
    wceq
    @31
    @42
    @43
    @52
    @44
    @45
    cI
    @4
    @5
    ccatcl
    syl2anc
    vx
    @32
    @21
    @34
    @18
    cE
    @19
    @32
    wceq
    @20
    @33
    cG
    cgsu
    @19
    @32
    cA
    coeq2
    oveq2d
    frmdup.e
    cG
    @20
    cgsu
    ovex
    #
    fvmpt3i
    syl
    eqtrd
    @31
    @42
    @43
    @12
    @39
    wceq
    @44
    @45
    @42
    @43
    @9
    @36
    @10
    @38
    @11
    vx
    @4
    @21
    @36
    @18
    cE
    @19
    @4
    wceq
    @20
    @35
    cG
    cgsu
    @19
    @4
    cA
    coeq2
    oveq2d
    frmdup.e
    @53
    fvmpt3i
    vx
    @5
    @21
    @38
    @18
    cE
    @19
    @5
    wceq
    @20
    @37
    cG
    cgsu
    @19
    @5
    cA
    coeq2
    oveq2d
    frmdup.e
    @53
    fvmpt3i
    oveqan12d
    syl2anc
    3eqtr4d
    ralrimivva
    c0
    @18
    wcel
    @16
    wph
    cI
    wrd0
    vx
    c0
    @21
    @15
    @18
    cE
    @19
    c0
    wceq
    #
    @21
    cG
    c0
    cgsu
    co
    @15
    @54
    @20
    c0
    cG
    cgsu
    @54
    @20
    cA
    c0
    ccom
    c0
    @19
    c0
    cA
    coeq2
    cA
    co02
    syl6eq
    oveq2d
    cG
    @15
    @15
    eqid
    #
    gsum0
    syl6eq
    frmdup.e
    @53
    fvmpt3i
    mp1i
    3jca
    vy
    vz
    @2
    cB
    @6
    @11
    cM
    cG
    cE
    @15
    c0
    @27
    frmdup.b
    @51
    @49
    cI
    cM
    frmdup.m
    frmd0
    @55
    ismhm
    sylanbrc
end
