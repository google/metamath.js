include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "ccycls.mm"
include "3pthd.mm"
include "wcel.mm"
include "wa.mm"
include "cs4.mm"
include "fveq1i.mm"
include "s4fv0.mm"
include "syl5eq.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "c3.mm"
include "cs3.mm"
include "fveq2i.mm"
include "s3len.mm"
include "eqtri.mm"
include "fveq12i.mm"
include "s4fv3.mm"
include "syl5req.mm"
include "adantl.mm"
include "ad2antlr.mm"
include "3eqtrd.mm"
include "syl2anc.mm"
include "iscycl.mm"
include "sylanbrc.mm"

theorem 3cycld
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


  assert |- ( ph -> F ( Cycles ` G ) P )

  proof
    wph
    cF
    cP
    cG
    cpths
    cfv
    wbr
    cc0
    cP
    cfv
    #
    cF
    chash
    cfv
    #
    cP
    cfv
    #
    wceq
    #
    cF
    cP
    cG
    ccycls
    cfv
    wbr
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
    3pthd
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
    #
    cA
    cD
    wceq
    #
    @3
    3wlkd.s
    3cycld.e
    @10
    @11
    wa
    @0
    cA
    cD
    @2
    @4
    @0
    cA
    wceq
    @5
    @9
    @11
    @4
    @0
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
    @12
    3wlkd.p
    fveq1i
    cA
    cB
    cC
    cD
    cV
    s4fv0
    syl5eq
    ad3antrrr
    @10
    @11
    simpr
    @9
    cD
    @2
    wceq
    #
    @6
    @11
    @8
    @13
    @7
    @8
    @2
    c3
    @12
    cfv
    cD
    @1
    c3
    cP
    @12
    3wlkd.p
    @1
    cJ
    cK
    cL
    cs3
    #
    chash
    cfv
    c3
    cF
    @14
    chash
    3wlkd.f
    fveq2i
    cJ
    cK
    cL
    s3len
    eqtri
    fveq12i
    cA
    cB
    cC
    cD
    cV
    s4fv3
    syl5req
    adantl
    ad2antlr
    3eqtrd
    syl2anc
    cP
    cF
    cG
    iscycl
    sylanbrc
end
