include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c3.mm"
include "wceq.mm"
include "cc0.mm"
include "3cycld.mm"
include "cs3.mm"
include "fveq2i.mm"
include "s3len.mm"
include "eqtri.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "cs4.mm"
include "fveq1i.mm"
include "s4fv0.mm"
include "syl5eq.mm"
include "ad2antrr.mm"
include "syl.mm"
include "3jca.mm"

theorem 3cyclpd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
  let cG: class G
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
  assume 3wlkd.v: |- V = ( Vtx ` G )
  assume 3wlkd.i: |- I = ( iEdg ` G )
  assume 3trld.n: |- ( ph -> ( J =/= K /\ J =/= L /\ K =/= L ) )
  assume 3cycld.e: |- ( ph -> A = D )


  assert |- ( ph -> ( F ( Cycles ` G ) P /\ ( # ` F ) = 3 /\ ( P ` 0 ) = A ) )

  proof
    wph
    cF
    cP
    cG
    ccycls
    cfv
    wbr
    cF
    chash
    cfv
    #
    c3
    wceq
    #
    cc0
    cP
    cfv
    #
    cA
    wceq
    #
    wph
    cA
    cB
    cC
    cD
    cP
    cF
    cG
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
    3wlkd.v
    3wlkd.i
    3trld.n
    3cycld.e
    3cycld
    @1
    wph
    @0
    cJ
    cK
    cL
    cs3
    #
    chash
    cfv
    c3
    cF
    @4
    chash
    3wlkd.f
    fveq2i
    cJ
    cK
    cL
    s3len
    eqtri
    a1i
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
    cC
    cV
    wcel
    cD
    cV
    wcel
    wa
    #
    wa
    @3
    3wlkd.s
    @5
    @3
    @6
    @7
    @5
    @2
    cc0
    cA
    cB
    cC
    cD
    cs4
    #
    cfv
    cA
    cc0
    cP
    @8
    3wlkd.p
    fveq1i
    cA
    cB
    cC
    cD
    cV
    s4fv0
    syl5eq
    ad2antrr
    syl
    3jca
end
