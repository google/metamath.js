include "cwlkson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cc0.mm"
include "clsw.mm"
include "3wlkd.mm"
include "wlkonwlk1l.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "c2.mm"
include "c3.mm"
include "3wlkdlem3.mm"
include "simpll.mm"
include "eqcomd.mm"
include "syl.mm"
include "cs4.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eleq1.mm"
include "mpbii.mm"
include "lsws4.mm"
include "syl5req.mm"
include "ad2antll.mm"
include "oveq12d.mm"
include "breqd.mm"
include "mpbird.mm"

theorem 3wlkond
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


  assert |- ( ph -> F ( A ( WalksOn ` G ) D ) P )

  proof
    wph
    cF
    cP
    cA
    cD
    cG
    cwlkson
    cfv
    #
    co
    #
    wbr
    cF
    cP
    cc0
    cP
    cfv
    #
    cP
    clsw
    cfv
    #
    @0
    co
    #
    wbr
    wph
    cP
    cF
    cG
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
    3wlkd
    wlkonwlk1l
    wph
    @1
    @4
    cF
    cP
    wph
    cA
    @2
    cD
    @3
    @0
    wph
    @2
    cA
    wceq
    #
    c1
    cP
    cfv
    cB
    wceq
    #
    wa
    #
    c2
    cP
    cfv
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
    #
    cA
    @2
    wceq
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
    #
    @12
    @2
    cA
    @5
    @6
    @11
    simpll
    eqcomd
    syl
    wph
    @12
    cD
    @3
    wceq
    #
    @13
    @10
    @14
    @7
    @8
    @10
    @3
    cA
    cB
    cC
    cD
    cs4
    #
    clsw
    cfv
    #
    cD
    cP
    @15
    clsw
    3wlkd.p
    fveq2i
    @10
    cD
    cvv
    wcel
    #
    @16
    cD
    wceq
    @10
    @9
    cvv
    wcel
    @17
    c3
    cP
    fvex
    @9
    cD
    cvv
    eleq1
    mpbii
    cA
    cB
    cC
    cD
    cvv
    lsws4
    syl
    syl5req
    ad2antll
    syl
    oveq12d
    breqd
    mpbird
end
