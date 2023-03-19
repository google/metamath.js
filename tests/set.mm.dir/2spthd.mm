include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "cspths.mm"
include "2trld.mm"
include "cs3.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "3anan32.mm"
include "sylanbrc.mm"
include "funcnvs3.mm"
include "syl2anc.mm"
include "wceq.mm"
include "a1i.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "mpbird.mm"
include "isspth.mm"

theorem 2spthd
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
  assume 2spthd.n: |- ( ph -> A =/= C )


  assert |- ( ph -> F ( SPaths ` G ) P )

  proof
    wph
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cP
    ccnv
    #
    wfun
    #
    cF
    cP
    cG
    cspths
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
    2trld.n
    2trld
    wph
    @1
    cA
    cB
    cC
    cs3
    #
    ccnv
    #
    wfun
    #
    wph
    cA
    cV
    wcel
    cB
    cV
    wcel
    cC
    cV
    wcel
    w3a
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    w3a
    #
    @4
    2wlkd.s
    wph
    @5
    @7
    wa
    @6
    @8
    2wlkd.n
    2spthd.n
    @5
    @6
    @7
    3anan32
    sylanbrc
    cA
    cB
    cC
    cV
    funcnvs3
    syl2anc
    wph
    @0
    @3
    wph
    cP
    @2
    cP
    @2
    wceq
    wph
    2wlkd.p
    a1i
    cnveqd
    funeqd
    mpbird
    cP
    cF
    cG
    isspth
    sylanbrc
end
