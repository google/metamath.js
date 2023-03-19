include "cvtx.mm"
include "cfv.mm"
include "wne.mm"
include "wa.mm"
include "wcel.mm"
include "w3a.mm"
include "cumgr.mm"
include "cpr.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "umgr2adedgwlklem.mm"
include "syl.mm"
include "simprd.mm"
include "simpld.mm"
include "wss.mm"
include "ssid.mm"
include "syl5sseqr.mm"
include "jca.mm"
include "eqid.mm"
include "2wlkond.mm"

theorem umgr2adedgwlkon
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  assume umgr2adedgwlk.e: |- E = ( Edg ` G )
  assume umgr2adedgwlk.i: |- I = ( iEdg ` G )
  assume umgr2adedgwlk.f: |- F = <" J K ">
  assume umgr2adedgwlk.p: |- P = <" A B C ">
  assume umgr2adedgwlk.g: |- ( ph -> G e. UMGraph )
  assume umgr2adedgwlk.a: |- ( ph -> ( { A , B } e. E /\ { B , C } e. E ) )
  assume umgr2adedgwlk.j: |- ( ph -> ( I ` J ) = { A , B } )
  assume umgr2adedgwlk.k: |- ( ph -> ( I ` K ) = { B , C } )


  assert |- ( ph -> F ( A ( WalksOn ` G ) C ) P )

  proof
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
    cG
    cvtx
    cfv
    #
    umgr2adedgwlk.p
    umgr2adedgwlk.f
    wph
    cA
    cB
    wne
    cB
    cC
    wne
    wa
    #
    cA
    @0
    wcel
    cB
    @0
    wcel
    cC
    @0
    wcel
    w3a
    #
    wph
    cG
    cumgr
    wcel
    #
    cA
    cB
    cpr
    #
    cE
    wcel
    #
    cB
    cC
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @1
    @2
    wa
    wph
    @3
    @5
    @7
    wa
    @8
    umgr2adedgwlk.g
    umgr2adedgwlk.a
    @3
    @5
    @7
    3anass
    sylanbrc
    cA
    cB
    cC
    cE
    cG
    umgr2adedgwlk.e
    umgr2adedgwlklem
    syl
    #
    simprd
    wph
    @1
    @2
    @9
    simpld
    wph
    @4
    cJ
    cI
    cfv
    #
    wss
    @6
    cK
    cI
    cfv
    #
    wss
    wph
    @4
    @4
    @10
    @4
    ssid
    umgr2adedgwlk.j
    syl5sseqr
    wph
    @6
    @6
    @11
    @6
    ssid
    umgr2adedgwlk.k
    syl5sseqr
    jca
    @0
    eqid
    umgr2adedgwlk.i
    2wlkond
end
