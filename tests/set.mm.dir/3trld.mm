include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "ctrls.mm"
include "3wlkd.mm"
include "cs3.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "3wlkdlem7.mm"
include "funcnvs3.mm"
include "syl2anc.mm"
include "cnveqi.mm"
include "funeqi.mm"
include "sylibr.mm"
include "istrl.mm"
include "sylanbrc.mm"

theorem 3trld
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


  assert |- ( ph -> F ( Trails ` G ) P )

  proof
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    ccnv
    #
    wfun
    #
    cF
    cP
    cG
    ctrls
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
    3wlkd
    wph
    cJ
    cK
    cL
    cs3
    #
    ccnv
    #
    wfun
    #
    @1
    wph
    cJ
    cvv
    wcel
    cK
    cvv
    wcel
    cL
    cvv
    wcel
    w3a
    cJ
    cK
    wne
    cJ
    cL
    wne
    cK
    cL
    wne
    w3a
    @4
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
    3wlkdlem7
    3trld.n
    cJ
    cK
    cL
    cvv
    funcnvs3
    syl2anc
    @0
    @3
    cF
    @2
    3wlkd.f
    cnveqi
    funeqi
    sylibr
    cP
    cF
    cG
    istrl
    sylanbrc
end
