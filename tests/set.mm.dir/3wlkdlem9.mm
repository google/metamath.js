include "cpr.mm"
include "cc0.mm"
include "cfv.mm"
include "wss.mm"
include "c1.mm"
include "c2.mm"
include "w3a.mm"
include "wceq.mm"
include "wb.mm"
include "3wlkdlem8.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "3anbi123d.mm"
include "syl.mm"
include "mpbird.mm"

theorem 3wlkdlem9
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cV: class V
  let vk: setvar k
  let vj: setvar j
  assume 3wlkd.p: |- P = <" A B C D ">
  assume 3wlkd.f: |- F = <" J K L ">
  assume 3wlkd.s: |- ( ph -> ( ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) )
  assume 3wlkd.n: |- ( ph -> ( ( A =/= B /\ A =/= C ) /\ ( B =/= C /\ B =/= D ) /\ C =/= D ) )
  assume 3wlkd.e: |- ( ph -> ( { A , B } C_ ( I ` J ) /\ { B , C } C_ ( I ` K ) /\ { C , D } C_ ( I ` L ) ) )


  assert |- ( ph -> ( { A , B } C_ ( I ` ( F ` 0 ) ) /\ { B , C } C_ ( I ` ( F ` 1 ) ) /\ { C , D } C_ ( I ` ( F ` 2 ) ) ) )

  proof
    wph
    cA
    cB
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
    cB
    cC
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
    cC
    cD
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
    @0
    cJ
    cI
    cfv
    #
    wss
    #
    @4
    cK
    cI
    cfv
    #
    wss
    #
    @8
    cL
    cI
    cfv
    #
    wss
    #
    w3a
    #
    3wlkd.e
    wph
    @1
    cJ
    wceq
    #
    @5
    cK
    wceq
    #
    @9
    cL
    wceq
    #
    w3a
    #
    @12
    @19
    wb
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
    3wlkdlem8
    @23
    @3
    @14
    @7
    @16
    @11
    @18
    @20
    @21
    @3
    @14
    wb
    @22
    @20
    @2
    @13
    @0
    @1
    cJ
    cI
    fveq2
    sseq2d
    3ad2ant1
    @21
    @20
    @7
    @16
    wb
    @22
    @21
    @6
    @15
    @4
    @5
    cK
    cI
    fveq2
    sseq2d
    3ad2ant2
    @22
    @20
    @11
    @18
    wb
    @21
    @22
    @10
    @17
    @8
    @9
    cL
    cI
    fveq2
    sseq2d
    3ad2ant3
    3anbi123d
    syl
    mpbird
end
