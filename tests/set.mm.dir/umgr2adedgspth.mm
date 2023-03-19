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
include "wceq.mm"
include "wi.mm"
include "fveq2.mm"
include "eqcoms.mm"
include "eqeq1d.mm"
include "eqtr2.mm"
include "ex.mm"
include "syl6bi.mm"
include "com13.mm"
include "sylc.mm"
include "eqcom.mm"
include "prcom.mm"
include "eqeq2i.mm"
include "bitri.mm"
include "umgrpredgv.mm"
include "anim12d.mm"
include "preqr1g.mm"
include "eqneqall.mm"
include "syl6ci.mm"
include "syl5bi.mm"
include "syld.mm"
include "neqne.mm"
include "pm2.61d1.mm"
include "2spthd.mm"

theorem umgr2adedgspth
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
  assume umgr2adedgspth.n: |- ( ph -> A =/= C )


  assert |- ( ph -> F ( SPaths ` G ) P )

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
    #
    cB
    @0
    wcel
    #
    cC
    @0
    wcel
    #
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
    @5
    wa
    wph
    @6
    @8
    @10
    wa
    #
    @11
    umgr2adedgwlk.g
    umgr2adedgwlk.a
    @6
    @8
    @10
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
    @5
    @13
    simpld
    wph
    @7
    cJ
    cI
    cfv
    #
    wss
    @9
    cK
    cI
    cfv
    #
    wss
    wph
    @7
    @7
    @14
    @7
    ssid
    umgr2adedgwlk.j
    syl5sseqr
    wph
    @9
    @9
    @15
    @9
    ssid
    umgr2adedgwlk.k
    syl5sseqr
    jca
    @0
    eqid
    #
    umgr2adedgwlk.i
    wph
    cJ
    cK
    wceq
    #
    cJ
    cK
    wne
    #
    wph
    @17
    @9
    @7
    wceq
    #
    @18
    wph
    @14
    @7
    wceq
    #
    @15
    @9
    wceq
    #
    @17
    @19
    wi
    umgr2adedgwlk.j
    umgr2adedgwlk.k
    @17
    @21
    @20
    @19
    @17
    @21
    @14
    @9
    wceq
    #
    @20
    @19
    wi
    @17
    @15
    @14
    @9
    @15
    @14
    wceq
    cK
    cJ
    cK
    cJ
    cI
    fveq2
    eqcoms
    eqeq1d
    @22
    @20
    @19
    @14
    @9
    @7
    eqtr2
    ex
    syl6bi
    com13
    sylc
    @19
    @7
    cC
    cB
    cpr
    #
    wceq
    #
    wph
    @18
    @19
    @7
    @9
    wceq
    @24
    @9
    @7
    eqcom
    @9
    @23
    @7
    cB
    cC
    prcom
    eqeq2i
    bitri
    wph
    @24
    cA
    cC
    wceq
    #
    cA
    cC
    wne
    @18
    wph
    @2
    @4
    wa
    #
    @24
    @25
    wi
    wph
    @6
    @12
    @26
    umgr2adedgwlk.g
    umgr2adedgwlk.a
    @6
    @8
    @2
    @10
    @4
    @6
    @8
    @2
    @6
    @8
    wa
    @2
    @3
    cE
    cG
    cA
    cB
    @0
    @16
    umgr2adedgwlk.e
    umgrpredgv
    simpld
    ex
    @6
    @10
    @4
    @6
    @10
    wa
    @3
    @4
    cE
    cG
    cB
    cC
    @0
    @16
    umgr2adedgwlk.e
    umgrpredgv
    simprd
    ex
    anim12d
    sylc
    cA
    cC
    cB
    @0
    @0
    preqr1g
    syl
    umgr2adedgspth.n
    @18
    cA
    cC
    eqneqall
    syl6ci
    syl5bi
    syld
    cJ
    cK
    neqne
    pm2.61d1
    umgr2adedgspth.n
    2spthd
end
