include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "wral.mm"
include "c2.mm"
include "c3.mm"
include "wa.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wceq.mm"
include "3wlkdlem3.mm"
include "simpl.mm"
include "eleq1d.mm"
include "simpr.mm"
include "anbi12d.mm"
include "biimparc.mm"
include "cvv.mm"
include "wb.mm"
include "c0ex.mm"
include "1ex.mm"
include "pm3.2i.mm"
include "fveq2.mm"
include "ralprg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "ex.mm"
include "2ex.mm"
include "3ex.mm"
include "im2anan9.mm"
include "sylc.mm"
include "cun.mm"
include "cs3.mm"
include "fveq2i.mm"
include "s3len.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "fz0to3un2pr.mm"
include "raleqi.mm"
include "ralunb.mm"
include "bitri.mm"
include "sylibr.mm"

theorem 3wlkdlem4
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cV: class V
  assume 3wlkd.p: |- P = <" A B C D ">
  assume 3wlkd.f: |- F = <" J K L ">
  assume 3wlkd.s: |- ( ph -> ( ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) )

  disjoint A k
  disjoint B k
  disjoint C k
  disjoint D k
  disjoint J k
  disjoint K k
  disjoint L k
  disjoint V k
  disjoint F k
  disjoint P k
  assert |- ( ph -> A. k e. ( 0 ... ( # ` F ) ) ( P ` k ) e. V )

  proof
    wph
    vk
    cv
    #
    cP
    cfv
    #
    cV
    wcel
    #
    vk
    cc0
    c1
    cpr
    #
    wral
    #
    @2
    vk
    c2
    c3
    cpr
    #
    wral
    #
    wa
    #
    @2
    vk
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    wral
    #
    wph
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cC
    cV
    wcel
    #
    cD
    cV
    wcel
    #
    wa
    #
    wa
    cc0
    cP
    cfv
    #
    cA
    wceq
    #
    c1
    cP
    cfv
    #
    cB
    wceq
    #
    wa
    #
    c2
    cP
    cfv
    #
    cC
    wceq
    #
    c3
    cP
    cfv
    #
    cD
    wceq
    #
    wa
    #
    wa
    @7
    3wlkd.s
    wph
    cA
    cB
    cC
    cD
    cP
    cF
    cJ
    cK
    cL
    cV
    3wlkd.p
    3wlkd.f
    3wlkd.s
    3wlkdlem3
    @13
    @21
    @4
    @16
    @26
    @6
    @13
    @21
    @4
    @13
    @21
    wa
    #
    @4
    @17
    cV
    wcel
    #
    @19
    cV
    wcel
    #
    wa
    #
    @21
    @30
    @13
    @21
    @28
    @11
    @29
    @12
    @21
    @17
    cA
    cV
    @18
    @20
    simpl
    eleq1d
    @21
    @19
    cB
    cV
    @18
    @20
    simpr
    eleq1d
    anbi12d
    biimparc
    cc0
    cvv
    wcel
    #
    c1
    cvv
    wcel
    #
    wa
    @4
    @30
    wb
    @27
    @31
    @32
    c0ex
    1ex
    pm3.2i
    @2
    @28
    @29
    vk
    cc0
    c1
    cvv
    cvv
    @0
    cc0
    wceq
    @1
    @17
    cV
    @0
    cc0
    cP
    fveq2
    eleq1d
    @0
    c1
    wceq
    @1
    @19
    cV
    @0
    c1
    cP
    fveq2
    eleq1d
    ralprg
    mp1i
    mpbird
    ex
    @16
    @26
    @6
    @16
    @26
    wa
    #
    @6
    @22
    cV
    wcel
    #
    @24
    cV
    wcel
    #
    wa
    #
    @26
    @36
    @16
    @26
    @34
    @14
    @35
    @15
    @26
    @22
    cC
    cV
    @23
    @25
    simpl
    eleq1d
    @26
    @24
    cD
    cV
    @23
    @25
    simpr
    eleq1d
    anbi12d
    biimparc
    c2
    cvv
    wcel
    #
    c3
    cvv
    wcel
    #
    wa
    @6
    @36
    wb
    @33
    @37
    @38
    2ex
    3ex
    pm3.2i
    @2
    @34
    @35
    vk
    c2
    c3
    cvv
    cvv
    @0
    c2
    wceq
    @1
    @22
    cV
    @0
    c2
    cP
    fveq2
    eleq1d
    @0
    c3
    wceq
    @1
    @24
    cV
    @0
    c3
    cP
    fveq2
    eleq1d
    ralprg
    mp1i
    mpbird
    ex
    im2anan9
    sylc
    @10
    @2
    vk
    @3
    @5
    cun
    #
    wral
    @7
    @2
    vk
    @9
    @39
    @9
    cc0
    c3
    cfz
    co
    @39
    @8
    c3
    cc0
    cfz
    @8
    cJ
    cK
    cL
    cs3
    #
    chash
    cfv
    c3
    cF
    @40
    chash
    3wlkd.f
    fveq2i
    cJ
    cK
    cL
    s3len
    eqtri
    oveq2i
    fz0to3un2pr
    eqtri
    raleqi
    @2
    vk
    @3
    @5
    ralunb
    bitri
    sylibr
end
