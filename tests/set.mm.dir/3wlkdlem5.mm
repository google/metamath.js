include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "wne.mm"
include "c2.mm"
include "c3.mm"
include "w3a.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "simpl.mm"
include "id.mm"
include "3anim123i.mm"
include "syl.mm"
include "wceq.mm"
include "wb.mm"
include "3wlkdlem3.mm"
include "simpr.mm"
include "neeq12d.mm"
include "adantr.mm"
include "adantl.mm"
include "3anbi123d.mm"
include "mpbird.mm"
include "ctp.mm"
include "3wlkdlem2.mm"
include "raleqi.mm"
include "c0ex.mm"
include "1ex.mm"
include "2ex.mm"
include "fveq2.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "1p1e2.mm"
include "2p1e3.mm"
include "raltp.mm"
include "bitri.mm"
include "sylibr.mm"

theorem 3wlkdlem5
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
  assume 3wlkd.n: |- ( ph -> ( ( A =/= B /\ A =/= C ) /\ ( B =/= C /\ B =/= D ) /\ C =/= D ) )

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
  assert |- ( ph -> A. k e. ( 0 ..^ ( # ` F ) ) ( P ` k ) =/= ( P ` ( k + 1 ) ) )

  proof
    wph
    cc0
    cP
    cfv
    #
    c1
    cP
    cfv
    #
    wne
    #
    @1
    c2
    cP
    cfv
    #
    wne
    #
    @3
    c3
    cP
    cfv
    #
    wne
    #
    w3a
    #
    vk
    cv
    #
    cP
    cfv
    #
    @8
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wne
    #
    vk
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    wral
    #
    wph
    @7
    cA
    cB
    wne
    #
    cB
    cC
    wne
    #
    cC
    cD
    wne
    #
    w3a
    #
    wph
    @15
    cA
    cC
    wne
    #
    wa
    #
    @16
    cB
    cD
    wne
    #
    wa
    #
    @17
    w3a
    @18
    3wlkd.n
    @20
    @15
    @22
    @16
    @17
    @17
    @15
    @19
    simpl
    @16
    @21
    simpl
    @17
    id
    3anim123i
    syl
    wph
    @0
    cA
    wceq
    #
    @1
    cB
    wceq
    #
    wa
    #
    @3
    cC
    wceq
    #
    @5
    cD
    wceq
    #
    wa
    #
    wa
    #
    @7
    @18
    wb
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
    @29
    @2
    @15
    @4
    @16
    @6
    @17
    @25
    @2
    @15
    wb
    @28
    @25
    @0
    cA
    @1
    cB
    @23
    @24
    simpl
    @23
    @24
    simpr
    #
    neeq12d
    adantr
    @29
    @1
    cB
    @3
    cC
    @25
    @24
    @28
    @30
    adantr
    @28
    @26
    @25
    @26
    @27
    simpl
    #
    adantl
    neeq12d
    @28
    @6
    @17
    wb
    @25
    @28
    @3
    cC
    @5
    cD
    @31
    @26
    @27
    simpr
    neeq12d
    adantl
    3anbi123d
    syl
    mpbird
    @14
    @12
    vk
    cc0
    c1
    c2
    ctp
    #
    wral
    @7
    @12
    vk
    @13
    @32
    cA
    cB
    cC
    cD
    cP
    cF
    cJ
    cK
    cL
    3wlkd.p
    3wlkd.f
    3wlkdlem2
    raleqi
    @12
    @2
    @4
    @6
    vk
    cc0
    c1
    c2
    c0ex
    1ex
    2ex
    @8
    cc0
    wceq
    #
    @9
    @0
    @11
    @1
    @8
    cc0
    cP
    fveq2
    @33
    @10
    c1
    cP
    @33
    @10
    cc0
    c1
    caddc
    co
    c1
    @8
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    neeq12d
    @8
    c1
    wceq
    #
    @9
    @1
    @11
    @3
    @8
    c1
    cP
    fveq2
    @34
    @10
    c2
    cP
    @34
    @10
    c1
    c1
    caddc
    co
    c2
    @8
    c1
    c1
    caddc
    oveq1
    1p1e2
    syl6eq
    fveq2d
    neeq12d
    @8
    c2
    wceq
    #
    @9
    @3
    @11
    @5
    @8
    c2
    cP
    fveq2
    @35
    @10
    c3
    cP
    @35
    @10
    c2
    c1
    caddc
    co
    c3
    @8
    c2
    c1
    caddc
    oveq1
    2p1e3
    syl6eq
    fveq2d
    neeq12d
    raltp
    bitri
    sylibr
end
