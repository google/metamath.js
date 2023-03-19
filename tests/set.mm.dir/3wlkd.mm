include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "cs4.mm"
include "s4cli.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cs3.mm"
include "s3cli.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "3wlkdlem1.mm"
include "3wlkdlem10.mm"
include "3wlkdlem5.mm"
include "wa.mm"
include "1vgrex.mm"
include "ad2antrr.mm"
include "syl.mm"
include "3wlkdlem4.mm"
include "wlkd.mm"

theorem 3wlkd
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


  assert |- ( ph -> F ( Walks ` G ) P )

  proof
    wph
    cP
    vk
    cF
    cG
    cI
    cV
    cvv
    cP
    cvv
    cword
    #
    wcel
    wph
    cP
    cA
    cB
    cC
    cD
    cs4
    @0
    3wlkd.p
    cA
    cB
    cC
    cD
    s4cli
    eqeltri
    a1i
    cF
    @0
    wcel
    wph
    cF
    cJ
    cK
    cL
    cs3
    @0
    3wlkd.f
    cJ
    cK
    cL
    s3cli
    eqeltri
    a1i
    cP
    chash
    cfv
    cF
    chash
    cfv
    c1
    caddc
    co
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
    3wlkd.p
    3wlkd.f
    3wlkdlem1
    a1i
    wph
    cA
    cB
    cC
    cD
    cP
    vk
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
    3wlkdlem10
    wph
    cA
    cB
    cC
    cD
    cP
    vk
    cF
    cJ
    cK
    cL
    cV
    3wlkd.p
    3wlkd.f
    3wlkd.s
    3wlkd.n
    3wlkdlem5
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
    cG
    cvv
    wcel
    #
    3wlkd.s
    @1
    @4
    @2
    @3
    cG
    cA
    cV
    3wlkd.v
    1vgrex
    ad2antrr
    syl
    3wlkd.v
    3wlkd.i
    wph
    cA
    cB
    cC
    cD
    cP
    vk
    cF
    cJ
    cK
    cL
    cV
    3wlkd.p
    3wlkd.f
    3wlkd.s
    3wlkdlem4
    wlkd
end
