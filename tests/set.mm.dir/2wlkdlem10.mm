include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "cpr.mm"
include "wss.mm"
include "c2.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "2wlkdlem9.mm"
include "wceq.mm"
include "w3a.mm"
include "wb.mm"
include "2wlkdlem3.mm"
include "preq12.mm"
include "3adant3.mm"
include "sseq1d.mm"
include "3adant1.mm"
include "anbi12d.mm"
include "syl.mm"
include "mpbird.mm"
include "2wlkdlem2.mm"
include "raleqi.mm"
include "c0ex.mm"
include "1ex.mm"
include "fveq2.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "sseq12d.mm"
include "1p1e2.mm"
include "ralpr.mm"
include "bitri.mm"
include "sylibr.mm"

theorem 2wlkdlem10
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let vj: setvar j
  assume 2wlkd.p: |- P = <" A B C ">
  assume 2wlkd.f: |- F = <" J K ">
  assume 2wlkd.s: |- ( ph -> ( A e. V /\ B e. V /\ C e. V ) )
  assume 2wlkd.n: |- ( ph -> ( A =/= B /\ B =/= C ) )
  assume 2wlkd.e: |- ( ph -> ( { A , B } C_ ( I ` J ) /\ { B , C } C_ ( I ` K ) ) )

  disjoint F k
  disjoint P k
  disjoint V k
  disjoint I k
  disjoint F j
  disjoint j k
  disjoint P j
  assert |- ( ph -> A. k e. ( 0 ..^ ( # ` F ) ) { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) )

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
    cpr
    #
    cc0
    cF
    cfv
    #
    cI
    cfv
    #
    wss
    #
    @1
    c2
    cP
    cfv
    #
    cpr
    #
    c1
    cF
    cfv
    #
    cI
    cfv
    #
    wss
    #
    wa
    #
    vk
    cv
    #
    cP
    cfv
    #
    @12
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    @12
    cF
    cfv
    #
    cI
    cfv
    #
    wss
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
    @11
    cA
    cB
    cpr
    #
    @4
    wss
    #
    cB
    cC
    cpr
    #
    @9
    wss
    #
    wa
    #
    wph
    cA
    cB
    cC
    cP
    cF
    cI
    cJ
    cK
    cV
    2wlkd.p
    2wlkd.f
    2wlkd.s
    2wlkd.n
    2wlkd.e
    2wlkdlem9
    wph
    @0
    cA
    wceq
    #
    @1
    cB
    wceq
    #
    @6
    cC
    wceq
    #
    w3a
    #
    @11
    @26
    wb
    wph
    cA
    cB
    cC
    cP
    cF
    cJ
    cK
    cV
    2wlkd.p
    2wlkd.f
    2wlkd.s
    2wlkdlem3
    @30
    @5
    @23
    @10
    @25
    @30
    @2
    @22
    @4
    @27
    @28
    @2
    @22
    wceq
    @29
    @0
    @1
    cA
    cB
    preq12
    3adant3
    sseq1d
    @30
    @7
    @24
    @9
    @28
    @29
    @7
    @24
    wceq
    @27
    @1
    @6
    cB
    cC
    preq12
    3adant1
    sseq1d
    anbi12d
    syl
    mpbird
    @21
    @19
    vk
    cc0
    c1
    cpr
    #
    wral
    @11
    @19
    vk
    @20
    @31
    cA
    cB
    cC
    cP
    cF
    cJ
    cK
    2wlkd.p
    2wlkd.f
    2wlkdlem2
    raleqi
    @19
    @5
    @10
    vk
    cc0
    c1
    c0ex
    1ex
    @12
    cc0
    wceq
    #
    @16
    @2
    @18
    @4
    @32
    @13
    @0
    @15
    @1
    @12
    cc0
    cP
    fveq2
    @32
    @14
    c1
    cP
    @32
    @14
    cc0
    c1
    caddc
    co
    c1
    @12
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    preq12d
    @32
    @17
    @3
    cI
    @12
    cc0
    cF
    fveq2
    fveq2d
    sseq12d
    @12
    c1
    wceq
    #
    @16
    @7
    @18
    @9
    @33
    @13
    @1
    @15
    @6
    @12
    c1
    cP
    fveq2
    @33
    @14
    c2
    cP
    @33
    @14
    c1
    c1
    caddc
    co
    c2
    @12
    c1
    c1
    caddc
    oveq1
    1p1e2
    syl6eq
    fveq2d
    preq12d
    @33
    @17
    @8
    cI
    @12
    c1
    cF
    fveq2
    fveq2d
    sseq12d
    ralpr
    bitri
    sylibr
end
