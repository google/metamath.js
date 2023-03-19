include "cpw.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "simpld.mm"
include "cvv.mm"
include "wcel.mm"
include "csdm.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "syl.mm"
include "canth2g.mm"
include "sdomdom.mm"
include "3syl.mm"
include "domtr.mm"
include "syl2anc.mm"
include "wo.mm"
include "wa.mm"
include "cgch.mm"
include "ccda.mm"
include "co.mm"
include "cen.mm"
include "adantr.mm"
include "com.mm"
include "pwcdaidm.mm"
include "simpr.mm"
include "gchdomtri.mm"
include "syl3anc.mm"
include "ex.mm"
include "pwdom.mm"
include "simprd.mm"
include "jaod.mm"
include "syld.mm"
include "jca.mm"

theorem gchaclem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume gchaclem.1: |- ( ph -> _om ~<_ A )
  assume gchaclem.3: |- ( ph -> ~P C e. GCH )
  assume gchaclem.4: |- ( ph -> ( A ~<_ C /\ ( B ~<_ ~P C -> ~P A ~<_ B ) ) )


  assert |- ( ph -> ( A ~<_ ~P C /\ ( B ~<_ ~P ~P C -> ~P A ~<_ B ) ) )

  proof
    wph
    cA
    cC
    cpw
    #
    cdom
    wbr
    #
    cB
    @0
    cpw
    cdom
    wbr
    #
    cA
    cpw
    #
    cB
    cdom
    wbr
    #
    wi
    wph
    cA
    cC
    cdom
    wbr
    #
    cC
    @0
    cdom
    wbr
    #
    @1
    wph
    @5
    cB
    @0
    cdom
    wbr
    #
    @4
    wi
    #
    gchaclem.4
    simpld
    #
    wph
    cC
    cvv
    wcel
    #
    cC
    @0
    csdm
    wbr
    @6
    wph
    @5
    @10
    @9
    cA
    cC
    cdom
    reldom
    brrelex2i
    syl
    cC
    cvv
    canth2g
    cC
    @0
    sdomdom
    3syl
    cA
    cC
    @0
    domtr
    syl2anc
    wph
    @2
    @0
    cB
    cdom
    wbr
    #
    @7
    wo
    #
    @4
    wph
    @2
    @12
    wph
    @2
    wa
    #
    @0
    cgch
    wcel
    #
    @0
    @0
    ccda
    co
    @0
    cen
    wbr
    #
    @2
    @12
    wph
    @14
    @2
    gchaclem.3
    adantr
    @13
    com
    cC
    cdom
    wbr
    #
    @15
    wph
    @16
    @2
    wph
    com
    cA
    cdom
    wbr
    @5
    @16
    gchaclem.1
    @9
    com
    cA
    cC
    domtr
    syl2anc
    adantr
    cC
    pwcdaidm
    syl
    wph
    @2
    simpr
    @0
    cB
    gchdomtri
    syl3anc
    ex
    wph
    @11
    @4
    @7
    wph
    @5
    @3
    @0
    cdom
    wbr
    #
    @11
    @4
    wi
    @9
    cA
    cC
    pwdom
    @17
    @11
    @4
    @3
    @0
    cB
    domtr
    ex
    3syl
    wph
    @5
    @8
    gchaclem.4
    simprd
    jaod
    syld
    jca
end
