include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "cspths.mm"
include "3trld.mm"
include "wa.mm"
include "ccnv.mm"
include "wfun.mm"
include "simpr.mm"
include "cs4.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wi.mm"
include "df-3an.mm"
include "simplbi2.mm"
include "3ad2ant1.mm"
include "mpan9.mm"
include "simpr2.mm"
include "simpr3.mm"
include "3jca.mm"
include "mpdan.mm"
include "funcnvs4.mm"
include "syl2anc.mm"
include "adantr.mm"
include "wceq.mm"
include "a1i.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "mpbird.mm"
include "isspth.mm"
include "sylanbrc.mm"

theorem 3spthd
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
  assume 3spthd.n: |- ( ph -> A =/= D )


  assert |- ( ph -> F ( SPaths ` G ) P )

  proof
    wph
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cF
    cP
    cG
    cspths
    cfv
    wbr
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
    3trld
    wph
    @0
    wa
    #
    @0
    cP
    ccnv
    #
    wfun
    #
    @1
    wph
    @0
    simpr
    @2
    @4
    cA
    cB
    cC
    cD
    cs4
    #
    ccnv
    #
    wfun
    #
    wph
    @7
    @0
    wph
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    cC
    cV
    wcel
    cD
    cV
    wcel
    wa
    wa
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cA
    cD
    wne
    #
    w3a
    #
    cB
    cC
    wne
    cB
    cD
    wne
    wa
    #
    cC
    cD
    wne
    #
    w3a
    #
    @7
    3wlkd.s
    wph
    @8
    @9
    wa
    #
    @12
    @13
    w3a
    #
    @14
    3wlkd.n
    wph
    @16
    wa
    @11
    @12
    @13
    wph
    @10
    @16
    @11
    3spthd.n
    @15
    @12
    @10
    @11
    wi
    @13
    @11
    @15
    @10
    @8
    @9
    @10
    df-3an
    simplbi2
    3ad2ant1
    mpan9
    wph
    @15
    @12
    @13
    simpr2
    wph
    @15
    @12
    @13
    simpr3
    3jca
    mpdan
    cA
    cB
    cC
    cD
    cV
    funcnvs4
    syl2anc
    adantr
    @2
    @3
    @6
    @2
    cP
    @5
    cP
    @5
    wceq
    @2
    3wlkd.p
    a1i
    cnveqd
    funeqd
    mpbird
    cP
    cF
    cG
    isspth
    sylanbrc
    mpdan
end
