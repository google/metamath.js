include "cmpt.mm"
include "eqid.mm"
include "fmptd.mm"
include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wb.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfbr.mm"
include "nfim.mm"
include "wceq.mm"
include "breq2.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "adantr.mm"
include "mpbird.mm"
include "o1co.mm"

theorem o1compt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let cF: class F
  let vz: setvar z
  assume o1compt.1: |- ( ph -> F : A --> CC )
  assume o1compt.2: |- ( ph -> F e. O(1) )
  assume o1compt.3: |- ( ( ph /\ y e. B ) -> C e. A )
  assume o1compt.4: |- ( ph -> B C_ RR )
  assume o1compt.5: |- ( ( ph /\ m e. RR ) -> E. x e. RR A. y e. B ( x <_ y -> m <_ C ) )

  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint C m
  disjoint C x
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint F m
  disjoint F x
  disjoint m z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint ph z
  disjoint F z
  assert |- ( ph -> ( F o. ( y e. B |-> C ) ) e. O(1) )

  proof
    wph
    vx
    vz
    cA
    cB
    vm
    cF
    vy
    cB
    cC
    cmpt
    #
    o1compt.1
    o1compt.2
    wph
    vy
    cB
    cC
    cA
    @0
    o1compt.3
    @0
    eqid
    #
    fmptd
    o1compt.4
    wph
    vm
    cv
    #
    cr
    wcel
    #
    wa
    vx
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    @2
    @5
    @0
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    vx
    cr
    wrex
    #
    @4
    vy
    cv
    #
    cle
    wbr
    #
    @2
    cC
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
    o1compt.5
    wph
    @11
    @17
    wb
    @3
    wph
    @10
    @16
    vx
    cr
    @10
    @13
    @2
    @12
    @0
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
    wph
    @16
    @9
    @20
    vz
    vy
    cB
    @6
    @8
    vy
    @6
    vy
    nfv
    vy
    @2
    @7
    cle
    vy
    @2
    nfcv
    vy
    cle
    nfcv
    vy
    cB
    cC
    @5
    nffvmpt1
    nfbr
    nfim
    @20
    vz
    nfv
    @5
    @12
    wceq
    #
    @6
    @13
    @8
    @19
    @5
    @12
    @4
    cle
    breq2
    @21
    @7
    @18
    @2
    cle
    @5
    @12
    @0
    fveq2
    breq2d
    imbi12d
    cbvral
    wph
    @20
    @15
    vy
    cB
    wph
    @12
    cB
    wcel
    #
    wa
    #
    @19
    @14
    @13
    @23
    @18
    cC
    @2
    cle
    @23
    @22
    cC
    cA
    wcel
    @18
    cC
    wceq
    wph
    @22
    simpr
    o1compt.3
    vy
    cB
    cC
    cA
    @0
    @1
    fvmpt2
    syl2anc
    breq2d
    imbi2d
    ralbidva
    syl5bb
    rexbidv
    adantr
    mpbird
    o1co
end
