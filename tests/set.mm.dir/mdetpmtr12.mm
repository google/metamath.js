include "cfv.mm"
include "ccom.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cmul.mm"
include "ccrg.mm"
include "wcel.mm"
include "cfn.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "cbvmpt2v.mm"
include "mdetpmtr1.mm"
include "syl22anc.mm"
include "cbs.mm"
include "eqid.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "csymg.mm"
include "symgfv.mm"
include "syl2anc.mm"
include "simp3.mm"
include "matecld.mm"
include "matbas2d.mm"
include "mdetpmtr2.mm"
include "eqidd.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "mpt2eq3dva.mm"
include "syl6reqr.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "crg.mm"
include "crngring.mm"
include "syl.mm"
include "zrhcopsgnelbas.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "mdetcl.mm"
include "ringass.mm"
include "syl13anc.mm"
include "zrhcofipsgn.mm"
include "zring.mm"
include "crh.mm"
include "cz.mm"
include "zrhrhm.mm"
include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "wss.mm"
include "1z.mm"
include "neg1z.mm"
include "prssi.mm"
include "mp2an.mm"
include "psgnran.mm"
include "sseldi.mm"
include "zringbas.mm"
include "zringmulr.mm"
include "rhmmul.mm"
include "eqtr3d.mm"
include "3eqtrd.mm"

theorem mdetpmtr12
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vk: setvar k
  let vl: setvar l
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  assume mdetpmtr.a: |- A = ( N Mat R )
  assume mdetpmtr.b: |- B = ( Base ` A )
  assume mdetpmtr.d: |- D = ( N maDet R )
  assume mdetpmtr.g: |- G = ( Base ` ( SymGrp ` N ) )
  assume mdetpmtr.s: |- S = ( pmSgn ` N )
  assume mdetpmtr.z: |- Z = ( ZRHom ` R )
  assume mdetpmtr.t: |- .x. = ( .r ` R )
  assume mdetpmtr12.e: |- E = ( i e. N , j e. N |-> ( ( P ` i ) M ( Q ` j ) ) )
  assume mdetmptr12.r: |- ( ph -> R e. CRing )
  assume mdetmptr12.n: |- ( ph -> N e. Fin )
  assume mdetmptr12.m: |- ( ph -> M e. B )
  assume mdetmptr12.p: |- ( ph -> P e. G )
  assume mdetmptr12.q: |- ( ph -> Q e. G )

  disjoint Q i
  disjoint Q j
  disjoint i j
  disjoint i ph
  disjoint j ph
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint G i
  disjoint G j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint Q k
  disjoint Q l
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint k ph
  disjoint l ph
  disjoint .x. p
  disjoint .x. q
  disjoint p q
  disjoint B p
  disjoint B x
  disjoint i p
  disjoint i x
  disjoint j p
  disjoint j x
  disjoint p x
  disjoint B q
  disjoint q x
  disjoint E p
  disjoint E x
  disjoint G p
  disjoint G q
  disjoint G x
  disjoint i q
  disjoint j q
  disjoint M k
  disjoint M l
  disjoint M p
  disjoint M q
  disjoint M x
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint k p
  disjoint k q
  disjoint k x
  disjoint l p
  disjoint l q
  disjoint l x
  disjoint N k
  disjoint N l
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint P k
  disjoint P l
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint R k
  disjoint R l
  disjoint R p
  disjoint R q
  disjoint R x
  disjoint S p
  disjoint S q
  disjoint Z p
  disjoint Z q
  assert |- ( ph -> ( D ` M ) = ( ( Z ` ( ( S ` P ) x. ( S ` Q ) ) ) .x. ( D ` E ) ) )

  proof
    wph
    cM
    cD
    cfv
    #
    cP
    cZ
    cS
    ccom
    #
    cfv
    #
    vk
    vl
    cN
    cN
    vk
    cv
    #
    cP
    cfv
    #
    vl
    cv
    #
    cM
    co
    #
    cmpt2
    #
    cD
    cfv
    #
    c.x
    co
    #
    @2
    cQ
    @1
    cfv
    #
    cE
    cD
    cfv
    #
    c.x
    co
    #
    c.x
    co
    #
    cP
    cS
    cfv
    #
    cQ
    cS
    cfv
    #
    cmul
    co
    cZ
    cfv
    #
    @11
    c.x
    co
    #
    wph
    cR
    ccrg
    wcel
    #
    cN
    cfn
    wcel
    #
    cM
    cB
    wcel
    #
    cP
    cG
    wcel
    #
    @0
    @9
    wceq
    mdetmptr12.r
    mdetmptr12.n
    mdetmptr12.m
    mdetmptr12.p
    cA
    cB
    cD
    cP
    cR
    cS
    c.x
    vi
    vj
    @7
    cG
    cM
    cN
    cZ
    mdetpmtr.a
    mdetpmtr.b
    mdetpmtr.d
    mdetpmtr.g
    mdetpmtr.s
    mdetpmtr.z
    mdetpmtr.t
    vk
    vl
    vi
    vj
    cN
    cN
    @6
    vi
    cv
    #
    cP
    cfv
    #
    vj
    cv
    #
    cM
    co
    @23
    @5
    cM
    co
    #
    @3
    @22
    wceq
    @4
    @23
    @5
    cM
    @3
    @22
    cP
    fveq2
    oveq1d
    #
    @5
    @24
    @23
    cM
    oveq2
    cbvmpt2v
    mdetpmtr1
    syl22anc
    wph
    @8
    @12
    @2
    c.x
    wph
    @8
    @10
    vi
    vj
    cN
    cN
    @22
    @24
    cQ
    cfv
    #
    @7
    co
    #
    cmpt2
    #
    cD
    cfv
    #
    c.x
    co
    #
    @12
    wph
    @18
    @19
    @7
    cB
    wcel
    cQ
    cG
    wcel
    #
    @8
    @31
    wceq
    mdetmptr12.r
    mdetmptr12.n
    wph
    vk
    vl
    cA
    cB
    @6
    cR
    cR
    cbs
    cfv
    #
    cN
    ccrg
    mdetpmtr.a
    @33
    eqid
    #
    mdetpmtr.b
    mdetmptr12.n
    mdetmptr12.r
    wph
    @3
    cN
    wcel
    #
    @5
    cN
    wcel
    #
    w3a
    #
    cA
    cB
    cR
    @4
    @5
    @33
    cM
    cN
    mdetpmtr.a
    @34
    mdetpmtr.b
    @37
    @21
    @35
    @4
    cN
    wcel
    wph
    @35
    @21
    @36
    mdetmptr12.p
    3ad2ant1
    wph
    @35
    @36
    simp2
    cN
    cG
    cP
    cN
    csymg
    cfv
    #
    @3
    @38
    eqid
    #
    mdetpmtr.g
    symgfv
    syl2anc
    wph
    @35
    @36
    simp3
    wph
    @35
    @20
    @36
    mdetmptr12.m
    3ad2ant1
    matecld
    matbas2d
    mdetmptr12.q
    cA
    cB
    cD
    cQ
    cR
    cS
    c.x
    vi
    vj
    @29
    cG
    @7
    cN
    cZ
    mdetpmtr.a
    mdetpmtr.b
    mdetpmtr.d
    mdetpmtr.g
    mdetpmtr.s
    mdetpmtr.z
    mdetpmtr.t
    @29
    eqid
    mdetpmtr2
    syl22anc
    wph
    @10
    @10
    @11
    @30
    c.x
    wph
    @10
    eqidd
    wph
    cE
    @29
    cD
    wph
    @29
    vi
    vj
    cN
    cN
    @23
    @27
    cM
    co
    #
    cmpt2
    #
    cE
    wph
    vi
    vj
    cN
    cN
    @28
    @40
    wph
    @22
    cN
    wcel
    #
    @24
    cN
    wcel
    #
    w3a
    #
    @42
    @27
    cN
    wcel
    #
    @28
    @40
    wceq
    wph
    @42
    @43
    simp2
    #
    @44
    @32
    @43
    @45
    wph
    @42
    @32
    @43
    mdetmptr12.q
    3ad2ant1
    wph
    @42
    @43
    simp3
    cN
    cG
    cQ
    @38
    @24
    @39
    mdetpmtr.g
    symgfv
    syl2anc
    #
    vk
    vl
    @22
    @27
    cN
    cN
    @6
    @40
    @7
    @25
    @26
    @5
    @27
    @23
    cM
    oveq2
    @7
    eqid
    @23
    @27
    cM
    ovex
    ovmpt2
    syl2anc
    mpt2eq3dva
    mdetpmtr12.e
    syl6reqr
    fveq2d
    oveq12d
    eqtr4d
    oveq2d
    wph
    @2
    @10
    c.x
    co
    #
    @11
    c.x
    co
    #
    @13
    @17
    wph
    cR
    crg
    wcel
    #
    @2
    @33
    wcel
    #
    @10
    @33
    wcel
    #
    @11
    @33
    wcel
    #
    @49
    @13
    wceq
    wph
    @18
    @50
    mdetmptr12.r
    cR
    crngring
    syl
    #
    wph
    @50
    @19
    @21
    @51
    @54
    mdetmptr12.n
    mdetmptr12.p
    cG
    cP
    cR
    cS
    cN
    cZ
    mdetpmtr.g
    mdetpmtr.s
    mdetpmtr.z
    zrhcopsgnelbas
    syl3anc
    wph
    @50
    @19
    @32
    @52
    @54
    mdetmptr12.n
    mdetmptr12.q
    cG
    cQ
    cR
    cS
    cN
    cZ
    mdetpmtr.g
    mdetpmtr.s
    mdetpmtr.z
    zrhcopsgnelbas
    syl3anc
    wph
    @18
    cE
    cB
    wcel
    @53
    mdetmptr12.r
    wph
    cE
    @41
    cB
    mdetpmtr12.e
    wph
    vi
    vj
    cA
    cB
    @40
    cR
    @33
    cN
    ccrg
    mdetpmtr.a
    @34
    mdetpmtr.b
    mdetmptr12.n
    mdetmptr12.r
    @44
    cA
    cB
    cR
    @23
    @27
    @33
    cM
    cN
    mdetpmtr.a
    @34
    mdetpmtr.b
    @44
    @21
    @42
    @23
    cN
    wcel
    wph
    @42
    @21
    @43
    mdetmptr12.p
    3ad2ant1
    @46
    cN
    cG
    cP
    @38
    @22
    @39
    mdetpmtr.g
    symgfv
    syl2anc
    @47
    wph
    @42
    @20
    @43
    mdetmptr12.m
    3ad2ant1
    matecld
    matbas2d
    syl5eqel
    cA
    cB
    cD
    cR
    @33
    cE
    cN
    mdetpmtr.d
    mdetpmtr.a
    mdetpmtr.b
    @34
    mdetcl
    syl2anc
    @33
    cR
    c.x
    @2
    @10
    @11
    @34
    mdetpmtr.t
    ringass
    syl13anc
    wph
    @48
    @16
    @11
    c.x
    wph
    @48
    @14
    cZ
    cfv
    #
    @15
    cZ
    cfv
    #
    c.x
    co
    #
    @16
    wph
    @2
    @55
    @10
    @56
    c.x
    wph
    @19
    @21
    @2
    @55
    wceq
    mdetmptr12.n
    mdetmptr12.p
    cG
    cP
    cR
    cS
    cN
    cZ
    mdetpmtr.g
    mdetpmtr.z
    mdetpmtr.s
    zrhcofipsgn
    syl2anc
    wph
    @19
    @32
    @10
    @56
    wceq
    mdetmptr12.n
    mdetmptr12.q
    cG
    cQ
    cR
    cS
    cN
    cZ
    mdetpmtr.g
    mdetpmtr.z
    mdetpmtr.s
    zrhcofipsgn
    syl2anc
    oveq12d
    wph
    cZ
    zring
    cR
    crh
    co
    wcel
    #
    @14
    cz
    wcel
    @15
    cz
    wcel
    @16
    @57
    wceq
    wph
    @50
    @58
    @54
    cR
    cZ
    mdetpmtr.z
    zrhrhm
    syl
    wph
    c1
    c1
    cneg
    #
    cpr
    #
    cz
    @14
    c1
    cz
    wcel
    @59
    cz
    wcel
    @60
    cz
    wss
    1z
    neg1z
    c1
    @59
    cz
    prssi
    mp2an
    #
    wph
    @19
    @21
    @14
    @60
    wcel
    mdetmptr12.n
    mdetmptr12.p
    cG
    cP
    cS
    cN
    mdetpmtr.g
    mdetpmtr.s
    psgnran
    syl2anc
    sseldi
    wph
    @60
    cz
    @15
    @61
    wph
    @19
    @32
    @15
    @60
    wcel
    mdetmptr12.n
    mdetmptr12.q
    cG
    cQ
    cS
    cN
    mdetpmtr.g
    mdetpmtr.s
    psgnran
    syl2anc
    sseldi
    @14
    @15
    zring
    cR
    cmul
    c.x
    cZ
    cz
    zringbas
    zringmulr
    mdetpmtr.t
    rhmmul
    syl3anc
    eqtr4d
    oveq1d
    eqtr3d
    3eqtrd
end
