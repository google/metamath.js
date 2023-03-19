include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "cs3.mm"
include "s3cli.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cs2.mm"
include "s2cli.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "2wlkdlem1.mm"
include "2wlkdlem10.mm"
include "2wlkdlem5.mm"
include "w3a.mm"
include "1vgrex.mm"
include "3ad2ant1.mm"
include "syl.mm"
include "2wlkdlem4.mm"
include "wlkd.mm"

theorem 2wlkd
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
    cs3
    @0
    2wlkd.p
    cA
    cB
    cC
    s3cli
    eqeltri
    a1i
    cF
    @0
    wcel
    wph
    cF
    cJ
    cK
    cs2
    @0
    2wlkd.f
    cJ
    cK
    s2cli
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
    cP
    cF
    cJ
    cK
    2wlkd.p
    2wlkd.f
    2wlkdlem1
    a1i
    wph
    cA
    cB
    cC
    cP
    vk
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
    2wlkdlem10
    wph
    cA
    cB
    cC
    cP
    vk
    cF
    cJ
    cK
    cV
    2wlkd.p
    2wlkd.f
    2wlkd.s
    2wlkd.n
    2wlkdlem5
    wph
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    cG
    cvv
    wcel
    #
    2wlkd.s
    @1
    @2
    @4
    @3
    cG
    cA
    cV
    2wlkd.v
    1vgrex
    3ad2ant1
    syl
    2wlkd.v
    2wlkd.i
    wph
    cA
    cB
    cC
    cP
    vk
    cF
    cJ
    cK
    cV
    2wlkd.p
    2wlkd.f
    2wlkd.s
    2wlkdlem4
    wlkd
end
