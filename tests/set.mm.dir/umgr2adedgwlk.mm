include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "w3a.mm"
include "cvtx.mm"
include "wne.mm"
include "wa.mm"
include "wcel.mm"
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
include "2wlkd.mm"
include "cs2.mm"
include "fveq2i.mm"
include "s2len.mm"
include "eqtri.mm"
include "a1i.mm"
include "cs3.mm"
include "s3fv0.mm"
include "s3fv1.mm"
include "s3fv2.mm"
include "3anim123i.mm"
include "fveq1i.mm"
include "eqeq2i.mm"
include "eqcom.mm"
include "bitri.mm"
include "3anbi123i.mm"
include "sylibr.mm"
include "3jca.mm"

theorem umgr2adedgwlk
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


  assert |- ( ph -> ( F ( Walks ` G ) P /\ ( # ` F ) = 2 /\ ( A = ( P ` 0 ) /\ B = ( P ` 1 ) /\ C = ( P ` 2 ) ) ) )

  proof
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    chash
    cfv
    #
    c2
    wceq
    #
    cA
    cc0
    cP
    cfv
    #
    wceq
    #
    cB
    c1
    cP
    cfv
    #
    wceq
    #
    cC
    c2
    cP
    cfv
    #
    wceq
    #
    w3a
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
    @9
    wcel
    #
    cB
    @9
    wcel
    #
    cC
    @9
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
    @10
    @14
    wa
    wph
    @15
    @17
    @19
    wa
    @20
    umgr2adedgwlk.g
    umgr2adedgwlk.a
    @15
    @17
    @19
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
    #
    wph
    @10
    @14
    @21
    simpld
    wph
    @16
    cJ
    cI
    cfv
    #
    wss
    @18
    cK
    cI
    cfv
    #
    wss
    wph
    @16
    @16
    @23
    @16
    ssid
    umgr2adedgwlk.j
    syl5sseqr
    wph
    @18
    @18
    @24
    @18
    ssid
    umgr2adedgwlk.k
    syl5sseqr
    jca
    @9
    eqid
    umgr2adedgwlk.i
    2wlkd
    @1
    wph
    @0
    cJ
    cK
    cs2
    #
    chash
    cfv
    c2
    cF
    @25
    chash
    umgr2adedgwlk.f
    fveq2i
    cJ
    cK
    s2len
    eqtri
    a1i
    wph
    cc0
    cA
    cB
    cC
    cs3
    #
    cfv
    #
    cA
    wceq
    #
    c1
    @26
    cfv
    #
    cB
    wceq
    #
    c2
    @26
    cfv
    #
    cC
    wceq
    #
    w3a
    #
    @8
    wph
    @14
    @33
    @22
    @11
    @28
    @12
    @30
    @13
    @32
    cA
    cB
    cC
    @9
    s3fv0
    cA
    cB
    cC
    @9
    s3fv1
    cA
    cB
    cC
    @9
    s3fv2
    3anim123i
    syl
    @3
    @28
    @5
    @30
    @7
    @32
    @3
    cA
    @27
    wceq
    @28
    @2
    @27
    cA
    cc0
    cP
    @26
    umgr2adedgwlk.p
    fveq1i
    eqeq2i
    cA
    @27
    eqcom
    bitri
    @5
    cB
    @29
    wceq
    @30
    @4
    @29
    cB
    c1
    cP
    @26
    umgr2adedgwlk.p
    fveq1i
    eqeq2i
    cB
    @29
    eqcom
    bitri
    @7
    cC
    @31
    wceq
    @32
    @6
    @31
    cC
    c2
    cP
    @26
    umgr2adedgwlk.p
    fveq1i
    eqeq2i
    cC
    @31
    eqcom
    bitri
    3anbi123i
    sylibr
    3jca
end
