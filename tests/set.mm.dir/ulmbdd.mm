include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cuz.mm"
include "wrex.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "ulmi.mm"
include "r19.2uz.mm"
include "wi.mm"
include "r19.26.mm"
include "caddc.mm"
include "peano2re.mm"
include "adantl.mm"
include "cc.mm"
include "wf.mm"
include "culm.mm"
include "ulmcl.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "abscld.mm"
include "cmap.mm"
include "simpllr.mm"
include "elmapi.mm"
include "subcld.mm"
include "readdcld.mm"
include "adantr.mm"
include "pncan3d.mm"
include "fveq2d.mm"
include "abstrid.mm"
include "eqbrtrrd.mm"
include "simplr.mm"
include "1re.mm"
include "simprrl.mm"
include "abssubd.mm"
include "simprrr.mm"
include "eqbrtrd.mm"
include "ltle.mm"
include "sylancl.mm"
include "mpd.mm"
include "le2addd.mm"
include "letrd.mm"
include "expr.mm"
include "ralimdva.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "syl5bir.mm"
include "expd.mm"
include "rexlimdva.mm"
include "cbvrexv.mm"
include "syl6ib.mm"
include "syl5.mm"

theorem ulmbdd
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vy: setvar y
  assume ulmbdd.z: |- Z = ( ZZ>= ` M )
  assume ulmbdd.m: |- ( ph -> M e. ZZ )
  assume ulmbdd.f: |- ( ph -> F : Z --> ( CC ^m S ) )
  assume ulmbdd.b: |- ( ( ph /\ k e. Z ) -> E. x e. RR A. z e. S ( abs ` ( ( F ` k ) ` z ) ) <_ x )
  assume ulmbdd.u: |- ( ph -> F ( ~~>u ` S ) G )

  disjoint k x
  disjoint k z
  disjoint F k
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint G k
  disjoint G x
  disjoint G z
  disjoint k ph
  disjoint ph x
  disjoint ph z
  disjoint S k
  disjoint S x
  disjoint S z
  disjoint M k
  disjoint M z
  disjoint Z k
  disjoint Z x
  disjoint Z z
  disjoint j k
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint j y
  disjoint G j
  disjoint k y
  disjoint x y
  disjoint y z
  disjoint G y
  disjoint j ph
  disjoint S j
  disjoint S y
  disjoint M j
  disjoint Z j
  assert |- ( ph -> E. x e. RR A. z e. S ( abs ` ( G ` z ) ) <_ x )

  proof
    wph
    vz
    cv
    #
    vk
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @0
    cG
    cfv
    #
    cmin
    co
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    vj
    cv
    cuz
    cfv
    wral
    vj
    cZ
    wrex
    #
    @4
    cabs
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vz
    cS
    wral
    #
    vx
    cr
    wrex
    #
    wph
    vz
    @4
    @3
    c1
    cS
    vj
    vk
    cF
    cG
    cM
    cZ
    ulmbdd.z
    ulmbdd.m
    ulmbdd.f
    wph
    @1
    cZ
    wcel
    #
    @0
    cS
    wcel
    #
    wa
    wa
    @3
    eqidd
    wph
    @15
    wa
    @4
    eqidd
    ulmbdd.u
    c1
    crp
    wcel
    wph
    1rp
    a1i
    ulmi
    @8
    @7
    vk
    cZ
    wrex
    wph
    @13
    @7
    vj
    vk
    cM
    cZ
    ulmbdd.z
    r19.2uz
    wph
    @7
    @13
    vk
    cZ
    wph
    @14
    wa
    #
    @7
    @9
    vy
    cv
    #
    cle
    wbr
    #
    vz
    cS
    wral
    #
    vy
    cr
    wrex
    #
    @13
    @16
    @3
    cabs
    cfv
    #
    @10
    cle
    wbr
    #
    vz
    cS
    wral
    #
    vx
    cr
    wrex
    @7
    @20
    wi
    #
    ulmbdd.b
    @16
    @23
    @24
    vx
    cr
    @16
    @10
    cr
    wcel
    #
    wa
    #
    @23
    @7
    @20
    @23
    @7
    wa
    @22
    @6
    wa
    #
    vz
    cS
    wral
    #
    @26
    @20
    @22
    @6
    vz
    cS
    r19.26
    @26
    @10
    c1
    caddc
    co
    #
    cr
    wcel
    #
    @28
    @9
    @29
    cle
    wbr
    #
    vz
    cS
    wral
    #
    @20
    @25
    @30
    @16
    @10
    peano2re
    adantl
    #
    @26
    @27
    @31
    vz
    cS
    @26
    @15
    @27
    @31
    @26
    @15
    @27
    wa
    #
    wa
    #
    @9
    @21
    @4
    @3
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    @29
    @35
    @4
    @35
    cS
    cc
    @0
    cG
    wph
    cS
    cc
    cG
    wf
    #
    @14
    @25
    @34
    wph
    cF
    cG
    cS
    culm
    cfv
    wbr
    @39
    ulmbdd.u
    cS
    cF
    cG
    ulmcl
    syl
    ad3antrrr
    @26
    @15
    @27
    simprl
    #
    ffvelrnd
    #
    abscld
    @35
    @21
    @37
    @35
    @3
    @35
    cS
    cc
    @0
    @2
    @35
    @2
    cc
    cS
    cmap
    co
    #
    wcel
    cS
    cc
    @2
    wf
    @35
    cZ
    @42
    @1
    cF
    wph
    cZ
    @42
    cF
    wf
    @14
    @25
    @34
    ulmbdd.f
    ad3antrrr
    wph
    @14
    @25
    @34
    simpllr
    ffvelrnd
    @2
    cc
    cS
    elmapi
    syl
    @40
    ffvelrnd
    #
    abscld
    #
    @35
    @36
    @35
    @4
    @3
    @41
    @43
    subcld
    #
    abscld
    #
    readdcld
    @26
    @30
    @34
    @33
    adantr
    @35
    @3
    @36
    caddc
    co
    #
    cabs
    cfv
    @9
    @38
    cle
    @35
    @47
    @4
    cabs
    @35
    @3
    @4
    @43
    @41
    pncan3d
    fveq2d
    @35
    @3
    @36
    @43
    @45
    abstrid
    eqbrtrrd
    @35
    @21
    @37
    @10
    c1
    @44
    @46
    @16
    @25
    @34
    simplr
    c1
    cr
    wcel
    #
    @35
    1re
    a1i
    @26
    @15
    @22
    @6
    simprrl
    @35
    @37
    c1
    clt
    wbr
    #
    @37
    c1
    cle
    wbr
    #
    @35
    @37
    @5
    c1
    clt
    @35
    @4
    @3
    @41
    @43
    abssubd
    @26
    @15
    @22
    @6
    simprrr
    eqbrtrd
    @35
    @37
    cr
    wcel
    @48
    @49
    @50
    wi
    @46
    1re
    @37
    c1
    ltle
    sylancl
    mpd
    le2addd
    letrd
    expr
    ralimdva
    @19
    @32
    vy
    @29
    cr
    @17
    @29
    wceq
    @18
    @31
    vz
    cS
    @17
    @29
    @9
    cle
    breq2
    ralbidv
    rspcev
    syl6an
    syl5bir
    expd
    rexlimdva
    mpd
    @19
    @12
    vy
    vx
    cr
    @17
    @10
    wceq
    @18
    @11
    vz
    cS
    @17
    @10
    @9
    cle
    breq2
    ralbidv
    cbvrexv
    syl6ib
    rexlimdva
    syl5
    mpd
end
