include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "wne.mm"
include "c2.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "wceq.mm"
include "w3a.mm"
include "wb.mm"
include "2wlkdlem3.mm"
include "simp1.mm"
include "simp2.mm"
include "neeq12d.mm"
include "simp3.mm"
include "anbi12d.mm"
include "bicomd.mm"
include "syl.mm"
include "mpbid.mm"
include "cpr.mm"
include "2wlkdlem2.mm"
include "raleqi.mm"
include "c0ex.mm"
include "1ex.mm"
include "fveq2.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "1p1e2.mm"
include "ralpr.mm"
include "bitri.mm"
include "sylibr.mm"

theorem 2wlkdlem5
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cK: class K
  let cV: class V
  assume 2wlkd.p: |- P = <" A B C ">
  assume 2wlkd.f: |- F = <" J K ">
  assume 2wlkd.s: |- ( ph -> ( A e. V /\ B e. V /\ C e. V ) )
  assume 2wlkd.n: |- ( ph -> ( A =/= B /\ B =/= C ) )

  disjoint F k
  disjoint P k
  disjoint V k
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
    wa
    #
    vk
    cv
    #
    cP
    cfv
    #
    @6
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
    cA
    cB
    wne
    #
    cB
    cC
    wne
    #
    wa
    #
    @5
    2wlkd.n
    wph
    @0
    cA
    wceq
    #
    @1
    cB
    wceq
    #
    @3
    cC
    wceq
    #
    w3a
    #
    @15
    @5
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
    @19
    @5
    @15
    @19
    @2
    @13
    @4
    @14
    @19
    @0
    cA
    @1
    cB
    @16
    @17
    @18
    simp1
    @16
    @17
    @18
    simp2
    #
    neeq12d
    @19
    @1
    cB
    @3
    cC
    @20
    @16
    @17
    @18
    simp3
    neeq12d
    anbi12d
    bicomd
    syl
    mpbid
    @12
    @10
    vk
    cc0
    c1
    cpr
    #
    wral
    @5
    @10
    vk
    @11
    @21
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
    @10
    @2
    @4
    vk
    cc0
    c1
    c0ex
    1ex
    @6
    cc0
    wceq
    #
    @7
    @0
    @9
    @1
    @6
    cc0
    cP
    fveq2
    @22
    @8
    c1
    cP
    @22
    @8
    cc0
    c1
    caddc
    co
    c1
    @6
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    neeq12d
    @6
    c1
    wceq
    #
    @7
    @1
    @9
    @3
    @6
    c1
    cP
    fveq2
    @23
    @8
    c2
    cP
    @23
    @8
    c1
    c1
    caddc
    co
    c2
    @6
    c1
    c1
    caddc
    oveq1
    1p1e2
    syl6eq
    fveq2d
    neeq12d
    ralpr
    bitri
    sylibr
end
