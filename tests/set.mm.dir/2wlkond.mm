include "cwlkson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cwlks.mm"
include "cc0.mm"
include "wceq.mm"
include "chash.mm"
include "2wlkd.mm"
include "wcel.mm"
include "simp1d.mm"
include "cs3.mm"
include "fveq1i.mm"
include "s3fv0.mm"
include "syl5eq.mm"
include "syl.mm"
include "c2.mm"
include "cs2.mm"
include "fveq2i.mm"
include "s2len.mm"
include "eqtri.mm"
include "fveq12i.mm"
include "simp3d.mm"
include "s3fv2.mm"
include "wa.mm"
include "cvv.mm"
include "cword.mm"
include "w3a.mm"
include "wb.mm"
include "3simpb.mm"
include "s2cli.mm"
include "eqeltri.mm"
include "s3cli.mm"
include "pm3.2i.mm"
include "iswlkon.mm"
include "sylancl.mm"
include "mpbir3and.mm"

theorem 2wlkond
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


  assert |- ( ph -> F ( A ( WalksOn ` G ) C ) P )

  proof
    wph
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
    cwlks
    cfv
    wbr
    #
    cc0
    cP
    cfv
    #
    cA
    wceq
    #
    cF
    chash
    cfv
    #
    cP
    cfv
    #
    cC
    wceq
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
    2wlkd
    wph
    cA
    cV
    wcel
    #
    @3
    wph
    @7
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    2wlkd.s
    simp1d
    @7
    @2
    cc0
    cA
    cB
    cC
    cs3
    #
    cfv
    cA
    cc0
    cP
    @10
    2wlkd.p
    fveq1i
    cA
    cB
    cC
    cV
    s3fv0
    syl5eq
    syl
    wph
    @5
    c2
    @10
    cfv
    #
    cC
    @4
    c2
    cP
    @10
    2wlkd.p
    @4
    cJ
    cK
    cs2
    #
    chash
    cfv
    c2
    cF
    @12
    chash
    2wlkd.f
    fveq2i
    cJ
    cK
    s2len
    eqtri
    fveq12i
    wph
    @9
    @11
    cC
    wceq
    wph
    @7
    @8
    @9
    2wlkd.s
    simp3d
    cA
    cB
    cC
    cV
    s3fv2
    syl
    syl5eq
    wph
    @7
    @9
    wa
    #
    cF
    cvv
    cword
    #
    wcel
    #
    cP
    @14
    wcel
    #
    wa
    @0
    @1
    @3
    @6
    w3a
    wb
    wph
    @7
    @8
    @9
    w3a
    @13
    2wlkd.s
    @7
    @8
    @9
    3simpb
    syl
    @15
    @16
    cF
    @12
    @14
    2wlkd.f
    cJ
    cK
    s2cli
    eqeltri
    cP
    @10
    @14
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
    @14
    cF
    cG
    cV
    @14
    2wlkd.v
    iswlkon
    sylancl
    mpbir3and
end
