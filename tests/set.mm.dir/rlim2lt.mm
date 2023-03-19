include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "cv.mm"
include "clt.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "cle.mm"
include "rlim2.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "simplr.mm"
include "simpl.mm"
include "sselda.mm"
include "ltle.mm"
include "syl2anc.mm"
include "imim1d.mm"
include "ralimdva.mm"
include "sylan.mm"
include "reximdva.mm"
include "ralimdv.mm"
include "sylbid.mm"
include "c1.mm"
include "caddc.mm"
include "peano2re.mm"
include "adantl.mm"
include "ltp1.mm"
include "ad2antlr.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem rlim2lt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let cD: class D
  assume rlim2.1: |- ( ph -> A. z e. A B e. CC )
  assume rlim2.2: |- ( ph -> A C_ RR )
  assume rlim2.3: |- ( ph -> C e. CC )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint ph w
  disjoint D w
  disjoint D y
  disjoint D z
  assert |- ( ph -> ( ( z e. A |-> B ) ~~>r C <-> A. x e. RR+ E. y e. RR A. z e. A ( y < z -> ( abs ` ( B - C ) ) < x ) ) )

  proof
    wph
    vz
    cA
    cB
    cmpt
    cC
    crli
    wbr
    #
    vy
    cv
    #
    vz
    cv
    #
    clt
    wbr
    #
    cB
    cC
    cmin
    co
    cabs
    cfv
    vx
    cv
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    #
    wph
    @0
    @1
    @2
    cle
    wbr
    #
    @4
    wi
    #
    vz
    cA
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    @8
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    rlim2.1
    rlim2.2
    rlim2.3
    rlim2
    wph
    @12
    @7
    vx
    crp
    wph
    @11
    @6
    vy
    cr
    wph
    cA
    cr
    wss
    #
    @1
    cr
    wcel
    #
    @11
    @6
    wi
    rlim2.2
    @13
    @14
    wa
    #
    @10
    @5
    vz
    cA
    @15
    @2
    cA
    wcel
    #
    wa
    #
    @3
    @9
    @4
    @17
    @14
    @2
    cr
    wcel
    #
    @3
    @9
    wi
    @13
    @14
    @16
    simplr
    #
    @15
    cA
    cr
    @2
    @13
    @14
    simpl
    sselda
    #
    @1
    @2
    ltle
    syl2anc
    imim1d
    ralimdva
    sylan
    reximdva
    ralimdv
    sylbid
    wph
    @8
    vw
    cv
    #
    @2
    cle
    wbr
    #
    @4
    wi
    #
    vz
    cA
    wral
    #
    vw
    cr
    wrex
    #
    vx
    crp
    wral
    @0
    wph
    @7
    @25
    vx
    crp
    wph
    @6
    @25
    vy
    cr
    wph
    @14
    wa
    @1
    c1
    caddc
    co
    #
    cr
    wcel
    #
    @6
    @26
    @2
    cle
    wbr
    #
    @4
    wi
    #
    vz
    cA
    wral
    #
    @25
    @14
    @27
    wph
    @1
    peano2re
    #
    adantl
    wph
    @13
    @14
    @6
    @30
    wi
    rlim2.2
    @15
    @5
    @29
    vz
    cA
    @17
    @28
    @3
    @4
    @17
    @1
    @26
    clt
    wbr
    #
    @28
    @3
    @14
    @32
    @13
    @16
    @1
    ltp1
    ad2antlr
    @17
    @14
    @27
    @18
    @32
    @28
    wa
    @3
    wi
    @19
    @14
    @27
    @13
    @16
    @31
    ad2antlr
    @20
    @1
    @26
    @2
    ltletr
    syl3anc
    mpand
    imim1d
    ralimdva
    sylan
    @24
    @30
    vw
    @26
    cr
    @21
    @26
    wceq
    #
    @23
    @29
    vz
    cA
    @33
    @22
    @28
    @4
    @21
    @26
    @2
    cle
    breq1
    imbi1d
    ralbidv
    rspcev
    syl6an
    rexlimdva
    ralimdv
    wph
    vx
    vw
    vz
    cA
    cB
    cC
    rlim2.1
    rlim2.2
    rlim2.3
    rlim2
    sylibrd
    impbid
end
