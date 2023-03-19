include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "cuz.mm"
include "cc.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "w3a.mm"
include "cz.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "wb.mm"
include "ulmval.mm"
include "syl.mm"
include "3anan12.mm"
include "cdm.mm"
include "fdm.mm"
include "sylan9req.mm"
include "syl5eqr.mm"
include "adantr.mm"
include "uz11.mm"
include "mpbid.mm"
include "eqcomd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "feq2d.mm"
include "biimparc.mm"
include "sylan.mm"
include "impbida.mm"
include "anbi1d.mm"
include "biantrurd.mm"
include "simp-4l.mm"
include "simpr.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "eqeltrd.mm"
include "uztrn2.mm"
include "syl12anc.mm"
include "sylancom.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "pm5.32da.mm"
include "3bitr3d.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "rexeqdv.mm"
include "ceqsrexv.mm"
include "3bitrd.mm"

theorem ulm2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vn: setvar n
  let cC: class C
  assume ulm2.z: |- Z = ( ZZ>= ` M )
  assume ulm2.m: |- ( ph -> M e. ZZ )
  assume ulm2.f: |- ( ph -> F : Z --> ( CC ^m S ) )
  assume ulm2.b: |- ( ( ph /\ ( k e. Z /\ z e. S ) ) -> ( ( F ` k ) ` z ) = B )
  assume ulm2.a: |- ( ( ph /\ z e. S ) -> ( G ` z ) = A )
  assume ulm2.g: |- ( ph -> G : S --> CC )
  assume ulm2.s: |- ( ph -> S e. V )

  disjoint j k
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint G j
  disjoint G k
  disjoint G x
  disjoint G z
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint M z
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint ph z
  disjoint A j
  disjoint A k
  disjoint A x
  disjoint B x
  disjoint S j
  disjoint S k
  disjoint S x
  disjoint S z
  disjoint Z j
  disjoint Z x
  disjoint j n
  disjoint k n
  disjoint n x
  disjoint n z
  disjoint F n
  disjoint G n
  disjoint M n
  disjoint n ph
  disjoint A n
  disjoint B n
  disjoint C j
  disjoint C k
  disjoint C x
  disjoint C z
  disjoint S n
  disjoint V n
  disjoint Z n
  assert |- ( ph -> ( F ( ~~>u ` S ) G <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) A. z e. S ( abs ` ( B - A ) ) < x ) )

  proof
    wph
    cF
    cG
    cS
    culm
    cfv
    wbr
    #
    vn
    cv
    #
    cuz
    cfv
    #
    cc
    cS
    cmap
    co
    #
    cF
    wf
    #
    cS
    cc
    cG
    wf
    #
    vz
    cv
    #
    vk
    cv
    #
    cF
    cfv
    cfv
    #
    @6
    cG
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
    vz
    cS
    wral
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    @2
    wrex
    #
    vx
    crp
    wral
    #
    w3a
    #
    vn
    cz
    wrex
    #
    @1
    cM
    wceq
    #
    cB
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @12
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    @16
    wral
    #
    vj
    @2
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    vn
    cz
    wrex
    #
    @27
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wph
    cS
    cV
    wcel
    @0
    @21
    wb
    ulm2.s
    vx
    vz
    cS
    vj
    vk
    vn
    cF
    cG
    cV
    ulmval
    syl
    wph
    @20
    @30
    vn
    cz
    @20
    @5
    @4
    @19
    wa
    #
    wa
    #
    wph
    @30
    @4
    @5
    @19
    3anan12
    wph
    @34
    @22
    @19
    wa
    @35
    @30
    wph
    @4
    @22
    @19
    wph
    @4
    @22
    wph
    @4
    wa
    #
    cM
    @1
    @36
    cM
    cuz
    cfv
    #
    @2
    wceq
    #
    cM
    @1
    wceq
    #
    @36
    @37
    cZ
    @2
    ulm2.z
    wph
    @4
    cZ
    cF
    cdm
    #
    @2
    wph
    cZ
    @3
    cF
    wf
    #
    @40
    cZ
    wceq
    ulm2.f
    cZ
    @3
    cF
    fdm
    syl
    @2
    @3
    cF
    fdm
    sylan9req
    syl5eqr
    @36
    cM
    cz
    wcel
    #
    @38
    @39
    wb
    wph
    @42
    @4
    ulm2.m
    adantr
    cM
    @1
    uz11
    syl
    mpbid
    eqcomd
    wph
    @41
    @22
    @4
    ulm2.f
    @22
    @4
    @41
    @22
    @2
    cZ
    @3
    cF
    @22
    @2
    @37
    cZ
    @1
    cM
    cuz
    fveq2
    ulm2.z
    syl6eqr
    #
    feq2d
    biimparc
    sylan
    impbida
    anbi1d
    wph
    @5
    @34
    ulm2.g
    biantrurd
    wph
    @22
    @19
    @29
    wph
    @22
    wa
    #
    @18
    @28
    vx
    crp
    @44
    @17
    @27
    vj
    @2
    @44
    @15
    @2
    wcel
    #
    wa
    #
    @14
    @26
    vk
    @16
    @46
    @7
    @16
    wcel
    #
    wa
    #
    @13
    @25
    vz
    cS
    @48
    @6
    cS
    wcel
    #
    wa
    #
    @11
    @24
    @12
    clt
    @50
    @10
    @23
    cabs
    @50
    @8
    cB
    @9
    cA
    cmin
    @50
    wph
    @7
    cZ
    wcel
    #
    @49
    @8
    cB
    wceq
    wph
    @22
    @45
    @47
    @49
    simp-4l
    #
    @48
    @51
    @49
    @46
    @15
    cZ
    wcel
    #
    @47
    @51
    @44
    @1
    cZ
    wcel
    @45
    @53
    @44
    @1
    cM
    cZ
    wph
    @22
    simpr
    wph
    cM
    cZ
    wcel
    @22
    wph
    cM
    @37
    cZ
    wph
    @42
    cM
    @37
    wcel
    ulm2.m
    cM
    uzid
    syl
    ulm2.z
    syl6eleqr
    adantr
    eqeltrd
    cM
    @15
    @1
    cZ
    ulm2.z
    uztrn2
    sylan
    cM
    @7
    @15
    cZ
    ulm2.z
    uztrn2
    sylan
    adantr
    @48
    @49
    simpr
    ulm2.b
    syl12anc
    @48
    @49
    wph
    @9
    cA
    wceq
    @52
    ulm2.a
    sylancom
    oveq12d
    fveq2d
    breq1d
    ralbidva
    ralbidva
    rexbidva
    ralbidv
    pm5.32da
    3bitr3d
    syl5bb
    rexbidv
    wph
    @42
    @31
    @33
    wb
    ulm2.m
    @29
    @33
    vn
    cM
    cz
    @22
    @28
    @32
    vx
    crp
    @22
    @27
    vj
    @2
    cZ
    @43
    rexeqdv
    ralbidv
    ceqsrexv
    syl
    3bitrd
end
