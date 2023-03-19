include "cc0.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "w3a.mm"
include "cv.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "wceq.mm"
include "wb.mm"
include "2wlkdlem3.mm"
include "simp1.mm"
include "eleq1d.mm"
include "simp2.mm"
include "simp3.mm"
include "3anbi123d.mm"
include "bicomd.mm"
include "syl.mm"
include "mpbid.mm"
include "ctp.mm"
include "cs2.mm"
include "fveq2i.mm"
include "s2len.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "fz0tp.mm"
include "raleqi.mm"
include "c0ex.mm"
include "1ex.mm"
include "2ex.mm"
include "fveq2.mm"
include "raltp.mm"
include "bitri.mm"
include "sylibr.mm"

theorem 2wlkdlem4
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

  disjoint F k
  disjoint P k
  disjoint V k
  assert |- ( ph -> A. k e. ( 0 ... ( # ` F ) ) ( P ` k ) e. V )

  proof
    wph
    cc0
    cP
    cfv
    #
    cV
    wcel
    #
    c1
    cP
    cfv
    #
    cV
    wcel
    #
    c2
    cP
    cfv
    #
    cV
    wcel
    #
    w3a
    #
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
    cC
    cV
    wcel
    #
    w3a
    #
    @6
    2wlkd.s
    wph
    @0
    cA
    wceq
    #
    @2
    cB
    wceq
    #
    @4
    cC
    wceq
    #
    w3a
    #
    @16
    @6
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
    @20
    @6
    @16
    @20
    @1
    @13
    @3
    @14
    @5
    @15
    @20
    @0
    cA
    cV
    @17
    @18
    @19
    simp1
    eleq1d
    @20
    @2
    cB
    cV
    @17
    @18
    @19
    simp2
    eleq1d
    @20
    @4
    cC
    cV
    @17
    @18
    @19
    simp3
    eleq1d
    3anbi123d
    bicomd
    syl
    mpbid
    @12
    @9
    vk
    cc0
    c1
    c2
    ctp
    #
    wral
    @6
    @9
    vk
    @11
    @21
    @11
    cc0
    c2
    cfz
    co
    @21
    @10
    c2
    cc0
    cfz
    @10
    cJ
    cK
    cs2
    #
    chash
    cfv
    c2
    cF
    @22
    chash
    2wlkd.f
    fveq2i
    cJ
    cK
    s2len
    eqtri
    oveq2i
    fz0tp
    eqtri
    raleqi
    @9
    @1
    @3
    @5
    vk
    cc0
    c1
    c2
    c0ex
    1ex
    2ex
    @7
    cc0
    wceq
    @8
    @0
    cV
    @7
    cc0
    cP
    fveq2
    eleq1d
    @7
    c1
    wceq
    @8
    @2
    cV
    @7
    c1
    cP
    fveq2
    eleq1d
    @7
    c2
    wceq
    @8
    @4
    cV
    @7
    c2
    cP
    fveq2
    eleq1d
    raltp
    bitri
    sylibr
end
