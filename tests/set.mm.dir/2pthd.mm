include "chash.mm"
include "cfv.mm"
include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "cs3.mm"
include "s3cli.mm"
include "eqeltri.mm"
include "a1i.mm"
include "c2.mm"
include "c3.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cs2.mm"
include "fveq2i.mm"
include "s2len.mm"
include "eqtri.mm"
include "3m1e2.mm"
include "s3len.mm"
include "eqtr2i.mm"
include "oveq1i.mm"
include "3eqtr2i.mm"
include "2pthdlem1.mm"
include "eqid.mm"
include "2trld.mm"
include "pthd.mm"

theorem 2pthd
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
    cs3
    #
    @1
    2wlkd.p
    cA
    cB
    cC
    s3cli
    eqeltri
    a1i
    @0
    c2
    c3
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
    cs2
    #
    chash
    cfv
    c2
    cF
    @4
    chash
    2wlkd.f
    fveq2i
    cJ
    cK
    s2len
    eqtri
    3m1e2
    c3
    @3
    c1
    cmin
    @3
    @2
    chash
    cfv
    c3
    cP
    @2
    chash
    2wlkd.p
    fveq2i
    cA
    cB
    cC
    s3len
    eqtr2i
    oveq1i
    3eqtr2i
    wph
    cA
    cB
    cC
    cP
    vj
    vk
    cF
    cJ
    cK
    cV
    2wlkd.p
    2wlkd.f
    2wlkd.s
    2wlkd.n
    2pthdlem1
    @0
    eqid
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
    pthd
end
