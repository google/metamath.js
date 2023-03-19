include "ctrlson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cwlkson.mm"
include "ctrls.mm"
include "3wlkond.mm"
include "3trld.mm"
include "wcel.mm"
include "cvv.mm"
include "cword.mm"
include "wa.mm"
include "wb.mm"
include "simplld.mm"
include "simprrd.mm"
include "cs3.mm"
include "s3cli.mm"
include "eqeltri.mm"
include "cs4.mm"
include "s4cli.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "istrlson.mm"
include "syl21anc.mm"
include "mpbir2and.mm"

theorem 3trlond
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


  assert |- ( ph -> F ( A ( TrailsOn ` G ) D ) P )

  proof
    wph
    cF
    cP
    cA
    cD
    cG
    ctrlson
    cfv
    co
    wbr
    #
    cF
    cP
    cA
    cD
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
    3wlkond
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
    cA
    cV
    wcel
    #
    cD
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
    wa
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
    cC
    cV
    wcel
    #
    @4
    wa
    3wlkd.s
    simplld
    wph
    @3
    @9
    wa
    @10
    @4
    3wlkd.s
    simprrd
    @8
    wph
    @6
    @7
    cF
    cJ
    cK
    cL
    cs3
    @5
    3wlkd.f
    cJ
    cK
    cL
    s3cli
    eqeltri
    cP
    cA
    cB
    cC
    cD
    cs4
    @5
    3wlkd.p
    cA
    cB
    cC
    cD
    s4cli
    eqeltri
    pm3.2i
    a1i
    cA
    cD
    cP
    @5
    cF
    cG
    cV
    @5
    3wlkd.v
    istrlson
    syl21anc
    mpbir2and
end
