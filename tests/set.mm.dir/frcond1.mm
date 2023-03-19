include "cfrgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wreu.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wne.mm"
include "w3a.mm"
include "wi.mm"
include "frgrusgrfrcond.mm"
include "wceq.mm"
include "preq2.mm"
include "preq1d.mm"
include "sseq1d.mm"
include "reubidv.mm"
include "preq2d.mm"
include "simp1.mm"
include "sneq.mm"
include "difeq2d.mm"
include "adantl.mm"
include "wa.mm"
include "necom.mm"
include "biimpi.mm"
include "anim2i.mm"
include "3adant1.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "rspc2vd.mm"
include "prcom.mm"
include "preq1i.mm"
include "sseq1i.mm"
include "reubii.mm"
include "syl6com.mm"
include "simplbiim.mm"

theorem frcond1
  let cA: class A
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let vb: setvar b
  let vk: setvar k
  let vl: setvar l
  assume frcond1.v: |- V = ( Vtx ` G )
  assume frcond1.e: |- E = ( Edg ` G )

  disjoint A b
  disjoint C b
  disjoint G b
  disjoint V b
  disjoint A k
  disjoint A l
  disjoint b k
  disjoint b l
  disjoint k l
  disjoint C k
  disjoint C l
  disjoint E k
  disjoint E l
  disjoint G k
  disjoint G l
  disjoint V k
  disjoint V l
  assert |- ( G e. FriendGraph -> ( ( A e. V /\ C e. V /\ A =/= C ) -> E! b e. V { { A , b } , { b , C } } C_ E ) )

  proof
    cG
    cfrgr
    wcel
    cG
    cusgr
    wcel
    vb
    cv
    #
    vk
    cv
    #
    cpr
    #
    @0
    vl
    cv
    #
    cpr
    #
    cpr
    #
    cE
    wss
    #
    vb
    cV
    wreu
    #
    vl
    cV
    @1
    csn
    #
    cdif
    #
    wral
    vk
    cV
    wral
    #
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    cA
    cC
    wne
    #
    w3a
    #
    cA
    @0
    cpr
    #
    @0
    cC
    cpr
    #
    cpr
    #
    cE
    wss
    #
    vb
    cV
    wreu
    #
    wi
    vb
    vk
    cE
    cG
    cV
    vl
    frcond1.v
    frcond1.e
    frgrusgrfrcond
    @14
    @10
    @0
    cA
    cpr
    #
    @16
    cpr
    #
    cE
    wss
    #
    vb
    cV
    wreu
    #
    @19
    @14
    @23
    @20
    @4
    cpr
    #
    cE
    wss
    #
    vb
    cV
    wreu
    @7
    vk
    vl
    cA
    cC
    cV
    @9
    cV
    cA
    csn
    #
    cdif
    #
    @1
    cA
    wceq
    #
    @6
    @25
    vb
    cV
    @28
    @5
    @24
    cE
    @28
    @2
    @20
    @4
    @1
    cA
    @0
    preq2
    preq1d
    sseq1d
    reubidv
    @3
    cC
    wceq
    #
    @25
    @22
    vb
    cV
    @29
    @24
    @21
    cE
    @29
    @4
    @16
    @20
    @3
    cC
    @0
    preq2
    preq2d
    sseq1d
    reubidv
    @11
    @12
    @13
    simp1
    @28
    @9
    @27
    wceq
    @14
    @28
    @8
    @26
    cV
    @1
    cA
    sneq
    difeq2d
    adantl
    @14
    @12
    cC
    cA
    wne
    #
    wa
    #
    cC
    @27
    wcel
    @12
    @13
    @31
    @11
    @13
    @30
    @12
    @13
    @30
    cA
    cC
    necom
    biimpi
    anim2i
    3adant1
    cC
    cV
    cA
    eldifsn
    sylibr
    rspc2vd
    @23
    @19
    @22
    @18
    vb
    cV
    @21
    @17
    cE
    @20
    @15
    @16
    @0
    cA
    prcom
    preq1i
    sseq1i
    reubii
    biimpi
    syl6com
    simplbiim
end
