include "cspthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "ctrlson.mm"
include "cspths.mm"
include "2trlond.mm"
include "2spthd.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cword.mm"
include "wb.mm"
include "w3a.mm"
include "3simpb.mm"
include "syl.mm"
include "cs2.mm"
include "s2cli.mm"
include "eqeltri.mm"
include "cs3.mm"
include "s3cli.mm"
include "pm3.2i.mm"
include "isspthson.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem 2pthond
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


  assert |- ( ph -> F ( A ( SPathsOn ` G ) C ) P )

  proof
    wph
    cF
    cP
    cA
    cC
    cG
    cspthson
    cfv
    co
    wbr
    #
    cF
    cP
    cA
    cC
    cG
    ctrlson
    cfv
    co
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
    2trlond
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
    2spthd.n
    2spthd
    wph
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    wa
    #
    cF
    cvv
    cword
    #
    wcel
    #
    cP
    @6
    wcel
    #
    wa
    @0
    @1
    @2
    wa
    wb
    wph
    @3
    cB
    cV
    wcel
    #
    @4
    w3a
    @5
    2wlkd.s
    @3
    @9
    @4
    3simpb
    syl
    @7
    @8
    cF
    cJ
    cK
    cs2
    @6
    2wlkd.f
    cJ
    cK
    s2cli
    eqeltri
    cP
    cA
    cB
    cC
    cs3
    @6
    2wlkd.p
    cA
    cB
    cC
    s3cli
    eqeltri
    pm3.2i
    cA
    cC
    cP
    @6
    cF
    cG
    cV
    @6
    2wlkd.v
    isspthson
    sylancl
    mpbir2and
end
