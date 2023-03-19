include "cwlkson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cwlks.mm"
include "cc0.mm"
include "wceq.mm"
include "chash.mm"
include "w3a.mm"
include "c2.mm"
include "c1.mm"
include "umgr2adedgwlk.mm"
include "simp1.mm"
include "id.mm"
include "eqcoms.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "biimpcd.mm"
include "com12.mm"
include "a1i.mm"
include "3imp.mm"
include "3jca.mm"
include "syl.mm"
include "cumgr.mm"
include "wcel.mm"
include "cvtx.mm"
include "cvv.mm"
include "cword.mm"
include "wa.mm"
include "wb.mm"
include "cpr.mm"
include "wne.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "umgr2adedgwlklem.mm"
include "3simpb.mm"
include "adantl.mm"
include "3syl.mm"
include "cs2.mm"
include "s2cli.mm"
include "eqeltri.mm"
include "cs3.mm"
include "s3cli.mm"
include "pm3.2i.mm"
include "3adant1.mm"
include "anim1i.mm"
include "eqid.mm"
include "iswlkon.mm"
include "sylancl.mm"
include "mpbird.mm"

theorem umgr2adedgwlkonALT
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
    w3a
    #
    wph
    @1
    @4
    c2
    wceq
    #
    cA
    @2
    wceq
    #
    cB
    c1
    cP
    cfv
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
    w3a
    #
    @7
    wph
    cA
    cB
    cC
    cP
    cE
    cF
    cG
    cI
    cJ
    cK
    umgr2adedgwlk.e
    umgr2adedgwlk.i
    umgr2adedgwlk.f
    umgr2adedgwlk.p
    umgr2adedgwlk.g
    umgr2adedgwlk.a
    umgr2adedgwlk.j
    umgr2adedgwlk.k
    umgr2adedgwlk
    @14
    @1
    @3
    @6
    @1
    @8
    @13
    simp1
    @13
    @1
    @3
    @8
    @9
    @10
    @3
    @12
    @3
    @2
    cA
    @3
    id
    eqcoms
    3ad2ant1
    3ad2ant3
    @1
    @8
    @13
    @6
    @8
    @13
    @6
    wi
    wi
    @1
    @13
    @8
    @6
    @12
    @9
    @8
    @6
    wi
    #
    @10
    @15
    @11
    cC
    @8
    @11
    cC
    wceq
    @6
    @8
    @11
    @5
    cC
    @11
    @5
    wceq
    c2
    @4
    c2
    @4
    cP
    fveq2
    eqcoms
    eqeq1d
    biimpcd
    eqcoms
    3ad2ant3
    com12
    a1i
    3imp
    3jca
    syl
    wph
    cG
    cumgr
    wcel
    #
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    cC
    @17
    wcel
    #
    w3a
    #
    cF
    cvv
    cword
    #
    wcel
    #
    cP
    @21
    wcel
    #
    wa
    #
    @0
    @7
    wb
    #
    wph
    @16
    @18
    @19
    wa
    #
    @20
    umgr2adedgwlk.g
    wph
    @16
    cA
    cB
    cpr
    cE
    wcel
    #
    cB
    cC
    cpr
    cE
    wcel
    #
    w3a
    #
    cA
    cB
    wne
    cB
    cC
    wne
    wa
    #
    @18
    cB
    @17
    wcel
    #
    @19
    w3a
    #
    wa
    @26
    wph
    @16
    @27
    @28
    wa
    @29
    umgr2adedgwlk.g
    umgr2adedgwlk.a
    @16
    @27
    @28
    3anass
    sylanbrc
    cA
    cB
    cC
    cE
    cG
    umgr2adedgwlk.e
    umgr2adedgwlklem
    @32
    @26
    @30
    @18
    @31
    @19
    3simpb
    adantl
    3syl
    @16
    @18
    @19
    3anass
    sylanbrc
    @22
    @23
    cF
    cJ
    cK
    cs2
    @21
    umgr2adedgwlk.f
    cJ
    cK
    s2cli
    eqeltri
    cP
    cA
    cB
    cC
    cs3
    @21
    umgr2adedgwlk.p
    cA
    cB
    cC
    s3cli
    eqeltri
    pm3.2i
    @20
    @24
    wa
    @26
    @24
    wa
    @25
    @20
    @26
    @24
    @18
    @19
    @26
    @16
    @26
    id
    3adant1
    anim1i
    cA
    cC
    cP
    @21
    cF
    cG
    @17
    @21
    @17
    eqid
    iswlkon
    syl
    sylancl
    mpbird
end
