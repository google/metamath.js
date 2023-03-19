include "cfv.mm"
include "wbr.mm"
include "ccom.mm"
include "wa.mm"
include "w3a.mm"
include "wfn.mm"
include "wf.mm"
include "fnfco.mm"
include "syl2anc.mm"
include "coass.mm"
include "breqi.mm"
include "sylibr.mm"
include "brcoffn.mm"
include "adantr.mm"
include "simprr.mm"
include "ex.mm"
include "jcai.mm"
include "simpll.mm"
include "simprl.mm"
include "3jca.mm"
include "syl.mm"

theorem brcofffn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume brcofffn.c: |- ( ph -> C Fn Z )
  assume brcofffn.d: |- ( ph -> D : Y --> Z )
  assume brcofffn.e: |- ( ph -> E : X --> Y )
  assume brcofffn.r: |- ( ph -> A ( C o. ( D o. E ) ) B )


  assert |- ( ph -> ( A E ( E ` A ) /\ ( E ` A ) D ( D ` ( E ` A ) ) /\ ( D ` ( E ` A ) ) C B ) )

  proof
    wph
    cA
    cA
    cE
    cfv
    #
    cE
    wbr
    #
    @0
    cB
    cC
    cD
    ccom
    #
    wbr
    #
    wa
    #
    @0
    @0
    cD
    cfv
    #
    cD
    wbr
    #
    @5
    cB
    cC
    wbr
    #
    wa
    #
    wa
    #
    @1
    @6
    @7
    w3a
    wph
    @4
    @8
    wph
    cA
    cB
    @2
    cE
    cX
    cY
    wph
    cC
    cZ
    wfn
    #
    cY
    cZ
    cD
    wf
    #
    @2
    cY
    wfn
    brcofffn.c
    brcofffn.d
    cZ
    cY
    cC
    cD
    fnfco
    syl2anc
    brcofffn.e
    wph
    cA
    cB
    cC
    cD
    cE
    ccom
    ccom
    #
    wbr
    cA
    cB
    @2
    cE
    ccom
    #
    wbr
    brcofffn.r
    cA
    cB
    @13
    @12
    cC
    cD
    cE
    coass
    breqi
    sylibr
    brcoffn
    wph
    @4
    @8
    wph
    @4
    wa
    @0
    cB
    cC
    cD
    cY
    cZ
    wph
    @10
    @4
    brcofffn.c
    adantr
    wph
    @11
    @4
    brcofffn.d
    adantr
    wph
    @1
    @3
    simprr
    brcoffn
    ex
    jcai
    @9
    @1
    @6
    @7
    @1
    @3
    @8
    simpll
    @4
    @6
    @7
    simprl
    @4
    @6
    @7
    simprr
    3jca
    syl
end
