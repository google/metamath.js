include "cpr.mm"
include "cc0.mm"
include "cfv.mm"
include "wss.mm"
include "c1.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "2wlkdlem8.mm"
include "fveq2.mm"
include "adantr.mm"
include "sseq2d.mm"
include "adantl.mm"
include "anbi12d.mm"
include "syl.mm"
include "mpbird.mm"

theorem 2wlkdlem9
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let vk: setvar k
  let vj: setvar j
  assume 2wlkd.p: |- P = <" A B C ">
  assume 2wlkd.f: |- F = <" J K ">
  assume 2wlkd.s: |- ( ph -> ( A e. V /\ B e. V /\ C e. V ) )
  assume 2wlkd.n: |- ( ph -> ( A =/= B /\ B =/= C ) )
  assume 2wlkd.e: |- ( ph -> ( { A , B } C_ ( I ` J ) /\ { B , C } C_ ( I ` K ) ) )


  assert |- ( ph -> ( { A , B } C_ ( I ` ( F ` 0 ) ) /\ { B , C } C_ ( I ` ( F ` 1 ) ) ) )

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
    wa
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
    wa
    #
    2wlkd.e
    wph
    @1
    cJ
    wceq
    #
    @5
    cK
    wceq
    #
    wa
    #
    @8
    @13
    wb
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
    2wlkdlem8
    @16
    @3
    @10
    @7
    @12
    @16
    @2
    @9
    @0
    @14
    @2
    @9
    wceq
    @15
    @1
    cJ
    cI
    fveq2
    adantr
    sseq2d
    @16
    @6
    @11
    @4
    @15
    @6
    @11
    wceq
    @14
    @5
    cK
    cI
    fveq2
    adantl
    sseq2d
    anbi12d
    syl
    mpbird
end
