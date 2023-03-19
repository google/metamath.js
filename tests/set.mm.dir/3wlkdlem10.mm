include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "cpr.mm"
include "wss.mm"
include "c2.mm"
include "c3.mm"
include "w3a.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "3wlkdlem9.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "3wlkdlem3.mm"
include "preq12.mm"
include "adantr.mm"
include "sseq1d.mm"
include "simplr.mm"
include "simprl.mm"
include "preq12d.mm"
include "adantl.mm"
include "3anbi123d.mm"
include "syl.mm"
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
include "sseq12d.mm"
include "1p1e2.mm"
include "2p1e3.mm"
include "raltp.mm"
include "bitri.mm"
include "sylibr.mm"

theorem 3wlkdlem10
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cV: class V
  let vj: setvar j
  assume 3wlkd.p: |- P = <" A B C D ">
  assume 3wlkd.f: |- F = <" J K L ">
  assume 3wlkd.s: |- ( ph -> ( ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) )
  assume 3wlkd.n: |- ( ph -> ( ( A =/= B /\ A =/= C ) /\ ( B =/= C /\ B =/= D ) /\ C =/= D ) )
  assume 3wlkd.e: |- ( ph -> ( { A , B } C_ ( I ` J ) /\ { B , C } C_ ( I ` K ) /\ { C , D } C_ ( I ` L ) ) )

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
    @6
    c3
    cP
    cfv
    #
    cpr
    #
    c2
    cF
    cfv
    #
    cI
    cfv
    #
    wss
    #
    w3a
    #
    vk
    cv
    #
    cP
    cfv
    #
    @17
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    @17
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
    @16
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
    cC
    cD
    cpr
    #
    @14
    wss
    #
    w3a
    #
    wph
    cA
    cB
    cC
    cD
    cP
    cF
    cI
    cJ
    cK
    cL
    cV
    3wlkd.p
    3wlkd.f
    3wlkd.s
    3wlkd.n
    3wlkd.e
    3wlkdlem9
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
    @6
    cC
    wceq
    #
    @11
    cD
    wceq
    #
    wa
    #
    wa
    #
    @16
    @33
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
    @40
    @5
    @28
    @10
    @30
    @15
    @32
    @40
    @2
    @27
    @4
    @36
    @2
    @27
    wceq
    @39
    @0
    @1
    cA
    cB
    preq12
    adantr
    sseq1d
    @40
    @7
    @29
    @9
    @40
    @1
    cB
    @6
    cC
    @34
    @35
    @39
    simplr
    @36
    @37
    @38
    simprl
    preq12d
    sseq1d
    @40
    @12
    @31
    @14
    @39
    @12
    @31
    wceq
    @36
    @6
    @11
    cC
    cD
    preq12
    adantl
    sseq1d
    3anbi123d
    syl
    mpbird
    @26
    @24
    vk
    cc0
    c1
    c2
    ctp
    #
    wral
    @16
    @24
    vk
    @25
    @41
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
    @24
    @5
    @10
    @15
    vk
    cc0
    c1
    c2
    c0ex
    1ex
    2ex
    @17
    cc0
    wceq
    #
    @21
    @2
    @23
    @4
    @42
    @18
    @0
    @20
    @1
    @17
    cc0
    cP
    fveq2
    @42
    @19
    c1
    cP
    @42
    @19
    cc0
    c1
    caddc
    co
    c1
    @17
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    preq12d
    @42
    @22
    @3
    cI
    @17
    cc0
    cF
    fveq2
    fveq2d
    sseq12d
    @17
    c1
    wceq
    #
    @21
    @7
    @23
    @9
    @43
    @18
    @1
    @20
    @6
    @17
    c1
    cP
    fveq2
    @43
    @19
    c2
    cP
    @43
    @19
    c1
    c1
    caddc
    co
    c2
    @17
    c1
    c1
    caddc
    oveq1
    1p1e2
    syl6eq
    fveq2d
    preq12d
    @43
    @22
    @8
    cI
    @17
    c1
    cF
    fveq2
    fveq2d
    sseq12d
    @17
    c2
    wceq
    #
    @21
    @12
    @23
    @14
    @44
    @18
    @6
    @20
    @11
    @17
    c2
    cP
    fveq2
    @44
    @19
    c3
    cP
    @44
    @19
    c2
    c1
    caddc
    co
    c3
    @17
    c2
    c1
    caddc
    oveq1
    2p1e3
    syl6eq
    fveq2d
    preq12d
    @44
    @22
    @13
    cI
    @17
    c2
    cF
    fveq2
    fveq2d
    sseq12d
    raltp
    bitri
    sylibr
end
