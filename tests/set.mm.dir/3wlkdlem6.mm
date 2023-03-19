include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "cpr.mm"
include "wss.mm"
include "c3.mm"
include "wceq.mm"
include "wa.mm"
include "3wlkdlem3.mm"
include "wb.mm"
include "preq12.mm"
include "sseq1d.mm"
include "adantr.mm"
include "ad2ant2lr.mm"
include "adantl.mm"
include "3anbi123d.mm"
include "syl5ibrcom.mm"
include "mpd.mm"
include "fvex.mm"
include "prss.mm"
include "simpl.mm"
include "sylbir.mm"
include "3anim123i.mm"
include "syl.mm"
include "eleq1.mm"
include "bicomd.mm"
include "mpbird.mm"

theorem 3wlkdlem6
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cF: class F
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


  assert |- ( ph -> ( A e. ( I ` J ) /\ B e. ( I ` K ) /\ C e. ( I ` L ) ) )

  proof
    wph
    cA
    cJ
    cI
    cfv
    #
    wcel
    #
    cB
    cK
    cI
    cfv
    #
    wcel
    #
    cC
    cL
    cI
    cfv
    #
    wcel
    #
    w3a
    #
    cc0
    cP
    cfv
    #
    @0
    wcel
    #
    c1
    cP
    cfv
    #
    @2
    wcel
    #
    c2
    cP
    cfv
    #
    @4
    wcel
    #
    w3a
    #
    wph
    @7
    @9
    cpr
    #
    @0
    wss
    #
    @9
    @11
    cpr
    #
    @2
    wss
    #
    @11
    c3
    cP
    cfv
    #
    cpr
    #
    @4
    wss
    #
    w3a
    #
    @13
    wph
    @7
    cA
    wceq
    #
    @9
    cB
    wceq
    #
    wa
    #
    @11
    cC
    wceq
    #
    @18
    cD
    wceq
    #
    wa
    #
    wa
    #
    @21
    wph
    cA
    cB
    cC
    cD
    cP
    cF
    cJ
    cK
    cL
    cV
    3wlkd.p
    3wlkd.f
    3wlkd.s
    3wlkdlem3
    #
    wph
    @21
    @28
    cA
    cB
    cpr
    #
    @0
    wss
    #
    cB
    cC
    cpr
    #
    @2
    wss
    #
    cC
    cD
    cpr
    #
    @4
    wss
    #
    w3a
    3wlkd.e
    @28
    @15
    @31
    @17
    @33
    @20
    @35
    @24
    @15
    @31
    wb
    @27
    @24
    @14
    @30
    @0
    @7
    @9
    cA
    cB
    preq12
    sseq1d
    adantr
    @28
    @16
    @32
    @2
    @23
    @25
    @16
    @32
    wceq
    @22
    @26
    @9
    @11
    cB
    cC
    preq12
    ad2ant2lr
    sseq1d
    @27
    @20
    @35
    wb
    @24
    @27
    @19
    @34
    @4
    @11
    @18
    cC
    cD
    preq12
    sseq1d
    adantl
    3anbi123d
    syl5ibrcom
    mpd
    @15
    @8
    @17
    @10
    @20
    @12
    @15
    @8
    @9
    @0
    wcel
    #
    wa
    @8
    @7
    @9
    @0
    cc0
    cP
    fvex
    c1
    cP
    fvex
    #
    prss
    @8
    @36
    simpl
    sylbir
    @17
    @10
    @11
    @2
    wcel
    #
    wa
    @10
    @9
    @11
    @2
    @37
    c2
    cP
    fvex
    #
    prss
    @10
    @38
    simpl
    sylbir
    @20
    @12
    @18
    @4
    wcel
    #
    wa
    @12
    @11
    @18
    @4
    @39
    c3
    cP
    fvex
    prss
    @12
    @40
    simpl
    sylbir
    3anim123i
    syl
    wph
    @28
    @6
    @13
    wb
    @29
    @28
    @13
    @6
    @28
    @8
    @1
    @10
    @3
    @12
    @5
    @24
    @8
    @1
    wb
    #
    @27
    @22
    @41
    @23
    @7
    cA
    @0
    eleq1
    adantr
    adantr
    @24
    @10
    @3
    wb
    #
    @27
    @23
    @42
    @22
    @9
    cB
    @2
    eleq1
    adantl
    adantr
    @27
    @12
    @5
    wb
    #
    @24
    @25
    @43
    @26
    @11
    cC
    @4
    eleq1
    adantr
    adantl
    3anbi123d
    bicomd
    syl
    mpbird
end
