include "ccom.mm"
include "co1.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "cabs.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cc.mm"
include "wf.mm"
include "wss.mm"
include "wb.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "o1dm.mm"
include "eqsstr3d.mm"
include "elo12.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wa.mm"
include "reeanv.mm"
include "ad3antrrr.mm"
include "ffvelrnda.mm"
include "breq2.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "sylan.mm"
include "an32s.mm"
include "adantr.mm"
include "fvco3.mm"
include "sylibrd.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "expimpd.mm"
include "ancomsd.mm"
include "reximdva.mm"
include "syl5bir.mm"
include "mpand.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "fco.mm"
include "mpbird.mm"

theorem o1co
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vm: setvar m
  let cF: class F
  let cG: class G
  let vn: setvar n
  let vz: setvar z
  assume o1co.1: |- ( ph -> F : A --> CC )
  assume o1co.2: |- ( ph -> F e. O(1) )
  assume o1co.3: |- ( ph -> G : B --> A )
  assume o1co.4: |- ( ph -> B C_ RR )
  assume o1co.5: |- ( ( ph /\ m e. RR ) -> E. x e. RR A. y e. B ( x <_ y -> m <_ ( G ` y ) ) )

  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint m n
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F n
  disjoint F z
  disjoint G n
  disjoint G z
  disjoint n ph
  disjoint B n
  assert |- ( ph -> ( F o. G ) e. O(1) )

  proof
    wph
    cF
    cG
    ccom
    #
    co1
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    @3
    @0
    cfv
    #
    cabs
    cfv
    #
    vn
    cv
    #
    cle
    wbr
    #
    wi
    #
    vy
    cB
    wral
    #
    vn
    cr
    wrex
    #
    vx
    cr
    wrex
    #
    wph
    vm
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    @14
    cF
    cfv
    #
    cabs
    cfv
    #
    @7
    cle
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vn
    cr
    wrex
    #
    vm
    cr
    wrex
    #
    @12
    wph
    cF
    co1
    wcel
    #
    @22
    o1co.2
    wph
    cA
    cc
    cF
    wf
    #
    cA
    cr
    wss
    @23
    @22
    wb
    o1co.1
    wph
    cA
    cF
    cdm
    #
    cr
    wph
    @24
    @25
    cA
    wceq
    o1co.1
    cA
    cc
    cF
    fdm
    syl
    wph
    @23
    @25
    cr
    wss
    o1co.2
    cF
    o1dm
    syl
    eqsstr3d
    vm
    vz
    cA
    vn
    cF
    elo12
    syl2anc
    mpbid
    wph
    @21
    @12
    vm
    cr
    wph
    @13
    cr
    wcel
    #
    wa
    #
    @4
    @13
    @3
    cG
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    cr
    wrex
    #
    @21
    @12
    o1co.5
    @32
    @21
    wa
    @31
    @20
    wa
    #
    vn
    cr
    wrex
    #
    vx
    cr
    wrex
    @27
    @12
    @31
    @20
    vx
    vn
    cr
    cr
    reeanv
    @27
    @34
    @11
    vx
    cr
    @27
    @2
    cr
    wcel
    #
    wa
    #
    @33
    @10
    vn
    cr
    @36
    @7
    cr
    wcel
    #
    wa
    #
    @20
    @31
    @10
    @38
    @20
    @31
    @10
    @38
    @20
    wa
    #
    @30
    @9
    vy
    cB
    @39
    @3
    cB
    wcel
    #
    wa
    #
    @29
    @8
    @4
    @41
    @29
    @28
    cF
    cfv
    #
    cabs
    cfv
    #
    @7
    cle
    wbr
    #
    @8
    @38
    @40
    @20
    @29
    @44
    wi
    #
    @38
    @40
    wa
    @28
    cA
    wcel
    @20
    @45
    @38
    cB
    cA
    @3
    cG
    wph
    cB
    cA
    cG
    wf
    #
    @26
    @35
    @37
    o1co.3
    ad3antrrr
    #
    ffvelrnda
    @19
    @45
    vz
    @28
    cA
    @14
    @28
    wceq
    #
    @15
    @29
    @18
    @44
    @14
    @28
    @13
    cle
    breq2
    @48
    @17
    @43
    @7
    cle
    @48
    @16
    @42
    cabs
    @14
    @28
    cF
    fveq2
    fveq2d
    breq1d
    imbi12d
    rspcva
    sylan
    an32s
    @41
    @6
    @43
    @7
    cle
    @41
    @5
    @42
    cabs
    @39
    @46
    @40
    @5
    @42
    wceq
    @38
    @46
    @20
    @47
    adantr
    cB
    cA
    @3
    cF
    cG
    fvco3
    sylan
    fveq2d
    breq1d
    sylibrd
    imim2d
    ralimdva
    expimpd
    ancomsd
    reximdva
    reximdva
    syl5bir
    mpand
    rexlimdva
    mpd
    wph
    cB
    cc
    @0
    wf
    #
    cB
    cr
    wss
    @1
    @12
    wb
    wph
    @24
    @46
    @49
    o1co.1
    o1co.3
    cB
    cA
    cc
    cF
    cG
    fco
    syl2anc
    o1co.4
    vx
    vy
    cB
    vn
    @0
    elo12
    syl2anc
    mpbird
end
