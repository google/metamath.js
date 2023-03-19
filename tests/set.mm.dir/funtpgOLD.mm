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
include "simp13.mm"
include "simp23.mm"
include "funsng.mm"
include "syl2anc.mm"
include "3ad2ant2.mm"
include "dmpropg.mm"
include "syl.mm"
include "dmsnopg.mm"
include "ineq12d.mm"
include "wn.mm"
include "wo.mm"
include "elpri.mm"
include "w3o.mm"
include "nne.mm"
include "biimpri.mm"
include "eqcoms.mm"
include "3mix2d.mm"
include "3mix3d.mm"
include "jaoi.mm"
include "3ianor.mm"
include "sylibr.mm"
include "con2i.mm"
include "disjsn.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"
include "funun.mm"
include "syl21anc.mm"
include "df-tp.mm"
include "funeqi.mm"

theorem funtpgOLD
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
    #
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
    @12
    @2
    @6
    @22
    @0
    @1
    @2
    @7
    @11
    simp13
    @3
    @4
    @5
    @6
    @11
    simp23
    #
    cZ
    cC
    cW
    cH
    funsng
    syl2anc
    @12
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
    @12
    @23
    @29
    @24
    @30
    @12
    @26
    @23
    @29
    wceq
    @7
    @3
    @26
    @11
    @27
    3ad2ant2
    cX
    cA
    cY
    cB
    cF
    cG
    dmpropg
    syl
    @12
    @6
    @24
    @30
    wceq
    @28
    cZ
    cC
    cH
    dmsnopg
    syl
    ineq12d
    @11
    @3
    @31
    c0
    wceq
    #
    @7
    @11
    cZ
    @29
    wcel
    #
    wn
    @32
    @33
    @11
    @33
    cZ
    cX
    wceq
    #
    cZ
    cY
    wceq
    #
    wo
    #
    @11
    wn
    #
    cZ
    cX
    cY
    elpri
    @36
    @8
    wn
    #
    @9
    wn
    #
    @10
    wn
    #
    w3o
    #
    @37
    @34
    @41
    @35
    @34
    @39
    @38
    @40
    @39
    cX
    cZ
    @39
    cX
    cZ
    wceq
    cX
    cZ
    nne
    biimpri
    eqcoms
    3mix2d
    @35
    @40
    @38
    @39
    @40
    cY
    cZ
    @40
    cY
    cZ
    wceq
    cY
    cZ
    nne
    biimpri
    eqcoms
    3mix3d
    jaoi
    @8
    @9
    @10
    3ianor
    sylibr
    syl
    con2i
    @29
    cZ
    disjsn
    sylibr
    3ad2ant3
    eqtrd
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
