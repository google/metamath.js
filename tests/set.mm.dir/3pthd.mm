include "chash.mm"
include "cfv.mm"
include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "cs4.mm"
include "s4cli.mm"
include "eqeltri.mm"
include "a1i.mm"
include "c3.mm"
include "c4.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cs3.mm"
include "fveq2i.mm"
include "s3len.mm"
include "eqtri.mm"
include "4m1e3.mm"
include "s4len.mm"
include "eqtr2i.mm"
include "oveq1i.mm"
include "3eqtr2i.mm"
include "3pthdlem1.mm"
include "eqid.mm"
include "3trld.mm"
include "pthd.mm"

theorem 3pthd
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


  assert |- ( ph -> F ( Paths ` G ) P )

  proof
    wph
    cP
    cF
    chash
    cfv
    #
    vk
    vj
    cF
    cG
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
    #
    @1
    3wlkd.p
    cA
    cB
    cC
    cD
    s4cli
    eqeltri
    a1i
    @0
    c3
    c4
    c1
    cmin
    co
    cP
    chash
    cfv
    #
    c1
    cmin
    co
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
    4m1e3
    c4
    @3
    c1
    cmin
    @3
    @2
    chash
    cfv
    c4
    cP
    @2
    chash
    3wlkd.p
    fveq2i
    cA
    cB
    cC
    cD
    s4len
    eqtr2i
    oveq1i
    3eqtr2i
    wph
    cA
    cB
    cC
    cD
    cP
    vj
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
    3pthdlem1
    @0
    eqid
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
    pthd
end
