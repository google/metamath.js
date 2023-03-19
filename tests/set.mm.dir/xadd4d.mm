include "cxad.mm"
include "co.mm"
include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "xaddass.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "simpld.mm"
include "xaddcld.mm"
include "xaddnemnf.mm"
include "syl2anc.mm"
include "syl112anc.mm"
include "xaddcom.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"

theorem xadd4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume xadd4d.1: |- ( ph -> ( A e. RR* /\ A =/= -oo ) )
  assume xadd4d.2: |- ( ph -> ( B e. RR* /\ B =/= -oo ) )
  assume xadd4d.3: |- ( ph -> ( C e. RR* /\ C =/= -oo ) )
  assume xadd4d.4: |- ( ph -> ( D e. RR* /\ D =/= -oo ) )


  assert |- ( ph -> ( ( A +e B ) +e ( C +e D ) ) = ( ( A +e C ) +e ( B +e D ) ) )

  proof
    wph
    cA
    cC
    cB
    cxad
    co
    #
    cD
    cxad
    co
    #
    cxad
    co
    #
    cA
    cC
    cB
    cD
    cxad
    co
    #
    cxad
    co
    #
    cxad
    co
    #
    cA
    cB
    cxad
    co
    cC
    cD
    cxad
    co
    #
    cxad
    co
    #
    cA
    cC
    cxad
    co
    @3
    cxad
    co
    #
    wph
    @1
    @4
    cA
    cxad
    wph
    cC
    cxr
    wcel
    #
    cC
    cmnf
    wne
    #
    wa
    #
    cB
    cxr
    wcel
    #
    cB
    cmnf
    wne
    #
    wa
    #
    cD
    cxr
    wcel
    #
    cD
    cmnf
    wne
    #
    wa
    #
    @1
    @4
    wceq
    xadd4d.3
    xadd4d.2
    xadd4d.4
    cC
    cB
    cD
    xaddass
    syl3anc
    oveq2d
    wph
    @7
    cA
    cB
    @6
    cxad
    co
    #
    cxad
    co
    #
    @2
    wph
    cA
    cxr
    wcel
    cA
    cmnf
    wne
    wa
    #
    @14
    @6
    cxr
    wcel
    @6
    cmnf
    wne
    #
    @7
    @19
    wceq
    xadd4d.1
    xadd4d.2
    wph
    cC
    cD
    wph
    @9
    @10
    xadd4d.3
    simpld
    #
    wph
    @15
    @16
    xadd4d.4
    simpld
    #
    xaddcld
    wph
    @11
    @17
    @21
    xadd4d.3
    xadd4d.4
    cC
    cD
    xaddnemnf
    syl2anc
    cA
    cB
    @6
    xaddass
    syl112anc
    wph
    @18
    @1
    cA
    cxad
    wph
    @1
    cB
    cC
    cxad
    co
    #
    cD
    cxad
    co
    #
    @18
    wph
    @0
    @24
    cD
    cxad
    wph
    @9
    @12
    @0
    @24
    wceq
    @22
    wph
    @12
    @13
    xadd4d.2
    simpld
    #
    cC
    cB
    xaddcom
    syl2anc
    oveq1d
    wph
    @14
    @11
    @17
    @25
    @18
    wceq
    xadd4d.2
    xadd4d.3
    xadd4d.4
    cB
    cC
    cD
    xaddass
    syl3anc
    eqtr2d
    oveq2d
    eqtrd
    wph
    @20
    @11
    @3
    cxr
    wcel
    @3
    cmnf
    wne
    #
    @8
    @5
    wceq
    xadd4d.1
    xadd4d.3
    wph
    cB
    cD
    @26
    @23
    xaddcld
    wph
    @14
    @17
    @27
    xadd4d.2
    xadd4d.4
    cB
    cD
    xaddnemnf
    syl2anc
    cA
    cC
    @3
    xaddass
    syl112anc
    3eqtr4d
end
