include "ctrlson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cwlkson.mm"
include "ctrls.mm"
include "2wlkond.mm"
include "2trld.mm"
include "wcel.mm"
include "cvv.mm"
include "cword.mm"
include "wa.mm"
include "wb.mm"
include "simp1d.mm"
include "simp3d.mm"
include "cs2.mm"
include "s2cli.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cs3.mm"
include "s3cli.mm"
include "istrlson.mm"
include "syl22anc.mm"
include "mpbir2and.mm"

theorem 2trlond
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


  assert |- ( ph -> F ( A ( TrailsOn ` G ) C ) P )

  proof
    wph
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
    cA
    cC
    cG
    cwlkson
    cfv
    co
    wbr
    #
    cF
    cP
    cG
    ctrls
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
    2wlkond
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
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    cF
    cvv
    cword
    #
    wcel
    #
    cP
    @5
    wcel
    #
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
    2wlkd.s
    simp1d
    wph
    @3
    @8
    @4
    2wlkd.s
    simp3d
    @6
    wph
    cF
    cJ
    cK
    cs2
    @5
    2wlkd.f
    cJ
    cK
    s2cli
    eqeltri
    a1i
    @7
    wph
    cP
    cA
    cB
    cC
    cs3
    @5
    2wlkd.p
    cA
    cB
    cC
    s3cli
    eqeltri
    a1i
    cA
    cC
    cP
    @5
    cF
    cG
    cV
    @5
    2wlkd.v
    istrlson
    syl22anc
    mpbir2and
end
