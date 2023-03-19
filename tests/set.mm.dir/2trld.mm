include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "ctrls.mm"
include "2wlkd.mm"
include "cs2.mm"
include "cvv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "2wlkdlem7.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "funcnvs2.mm"
include "syl.mm"
include "cnveqi.mm"
include "funeqi.mm"
include "sylibr.mm"
include "istrl.mm"

theorem 2trld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cF: class F
  let cG: class G
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
  assume 2wlkd.v: |- V = ( Vtx ` G )
  assume 2wlkd.i: |- I = ( iEdg ` G )
  assume 2trld.n: |- ( ph -> J =/= K )


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
    cP
    cF
    cG
    cI
    cJ
    cK
    cV
    2wlkd.p
    2wlkd.f
    2wlkd.s
    2wlkd.n
    2wlkd.e
    2wlkd.v
    2wlkd.i
    2wlkd
    wph
    cJ
    cK
    cs2
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
    #
    cK
    cvv
    wcel
    #
    cJ
    cK
    wne
    #
    w3a
    #
    @4
    wph
    @5
    @6
    wa
    @7
    @8
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
    2wlkdlem7
    2trld.n
    @5
    @6
    @7
    df-3an
    sylanbrc
    cJ
    cK
    cvv
    funcnvs2
    syl
    @0
    @3
    cF
    @2
    2wlkd.f
    cnveqi
    funeqi
    sylibr
    cP
    cF
    cG
    istrl
    sylanbrc
end
