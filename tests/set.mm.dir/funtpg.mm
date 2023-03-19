include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "cop.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "wfun.mm"
include "ctp.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "3simpa.mm"
include "simp1.mm"
include "funprg.mm"
include "syl3an.mm"
include "simp3.mm"
include "funsng.mm"
include "syl2an.mm"
include "3adant3.mm"
include "dmpropg.mm"
include "dmsnopg.mm"
include "ineqan12d.mm"
include "3impa.mm"
include "disjprsn.mm"
include "3adant1.mm"
include "sylan9eq.mm"
include "funun.mm"
include "syl21anc.mm"
include "df-tp.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem funtpg
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( ( ( X e. U /\ Y e. V /\ Z e. W ) /\ ( A e. F /\ B e. G /\ C e. H ) /\ ( X =/= Y /\ X =/= Z /\ Y =/= Z ) ) -> Fun { <. X , A >. , <. Y , B >. , <. Z , C >. } )

  proof
    cX
    cU
    wcel
    #
    cY
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    w3a
    #
    cA
    cF
    wcel
    #
    cB
    cG
    wcel
    #
    cC
    cH
    wcel
    #
    w3a
    #
    cX
    cY
    wne
    #
    cX
    cZ
    wne
    #
    cY
    cZ
    wne
    #
    w3a
    #
    w3a
    #
    cX
    cA
    cop
    #
    cY
    cB
    cop
    #
    cpr
    #
    cZ
    cC
    cop
    #
    csn
    #
    cun
    #
    wfun
    #
    @13
    @14
    @16
    ctp
    #
    wfun
    @12
    @15
    wfun
    #
    @17
    wfun
    #
    @15
    cdm
    #
    @17
    cdm
    #
    cin
    #
    c0
    wceq
    #
    @19
    @3
    @0
    @1
    wa
    @7
    @4
    @5
    wa
    #
    @11
    @8
    @21
    @0
    @1
    @2
    3simpa
    @4
    @5
    @6
    3simpa
    @8
    @9
    @10
    simp1
    cX
    cY
    cA
    cB
    cU
    cV
    cF
    cG
    funprg
    syl3an
    @3
    @7
    @22
    @11
    @3
    @2
    @6
    @22
    @7
    @0
    @1
    @2
    simp3
    @4
    @5
    @6
    simp3
    cZ
    cC
    cW
    cH
    funsng
    syl2an
    3adant3
    @7
    @11
    @26
    @3
    @7
    @11
    @25
    cX
    cY
    cpr
    #
    cZ
    csn
    #
    cin
    #
    c0
    @4
    @5
    @6
    @25
    @30
    wceq
    @27
    @6
    @23
    @28
    @24
    @29
    cX
    cA
    cY
    cB
    cF
    cG
    dmpropg
    cZ
    cC
    cH
    dmsnopg
    ineqan12d
    3impa
    @9
    @10
    @30
    c0
    wceq
    @8
    cX
    cY
    cZ
    disjprsn
    3adant1
    sylan9eq
    3adant1
    @15
    @17
    funun
    syl21anc
    @20
    @18
    @13
    @14
    @16
    df-tp
    funeqi
    sylibr
end
