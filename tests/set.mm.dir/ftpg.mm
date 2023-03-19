include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "cop.mm"
include "wf.mm"
include "ctp.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "3simpa.mm"
include "simp1.mm"
include "fprg.mm"
include "syl3an.mm"
include "eqidd.mm"
include "wb.mm"
include "simp3.mm"
include "anim12i.mm"
include "3adant3.mm"
include "fsng.mm"
include "syl.mm"
include "mpbird.mm"
include "wn.mm"
include "wo.mm"
include "elpri.mm"
include "eqcom.mm"
include "nne.mm"
include "bitr4i.mm"
include "orbi12i.mm"
include "ianor.mm"
include "sylbb2.mm"
include "con2i.mm"
include "3adant1.mm"
include "3ad2ant3.mm"
include "disjsn.mm"
include "sylibr.mm"
include "fun.mm"
include "syl21anc.mm"
include "df-tp.mm"
include "feq1i.mm"
include "feq23i.mm"
include "bitri.mm"

theorem ftpg
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


  assert |- ( ( ( X e. U /\ Y e. V /\ Z e. W ) /\ ( A e. F /\ B e. G /\ C e. H ) /\ ( X =/= Y /\ X =/= Z /\ Y =/= Z ) ) -> { <. X , A >. , <. Y , B >. , <. Z , C >. } : { X , Y , Z } --> { A , B , C } )

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
    cY
    cpr
    #
    cZ
    csn
    #
    cun
    #
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cun
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
    wf
    #
    cX
    cY
    cZ
    ctp
    #
    cA
    cB
    cC
    ctp
    #
    @19
    @20
    @22
    ctp
    #
    wf
    #
    @12
    @13
    @16
    @21
    wf
    #
    @14
    @17
    @23
    wf
    #
    @13
    @14
    cin
    c0
    wceq
    #
    @25
    @3
    @0
    @1
    wa
    @7
    @4
    @5
    wa
    @11
    @8
    @30
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
    fprg
    syl3an
    @12
    @31
    @23
    @23
    wceq
    #
    @12
    @23
    eqidd
    @12
    @2
    @6
    wa
    #
    @31
    @33
    wb
    @3
    @7
    @34
    @11
    @3
    @2
    @7
    @6
    @0
    @1
    @2
    simp3
    @4
    @5
    @6
    simp3
    anim12i
    3adant3
    cZ
    cC
    cW
    cH
    @23
    fsng
    syl
    mpbird
    @12
    cZ
    @13
    wcel
    #
    wn
    #
    @32
    @11
    @3
    @36
    @7
    @9
    @10
    @36
    @8
    @35
    @9
    @10
    wa
    #
    @35
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
    @37
    wn
    #
    cZ
    cX
    cY
    elpri
    @40
    @9
    wn
    #
    @10
    wn
    #
    wo
    @41
    @38
    @42
    @39
    @43
    @38
    cX
    cZ
    wceq
    @42
    cZ
    cX
    eqcom
    cX
    cZ
    nne
    bitr4i
    @39
    cY
    cZ
    wceq
    @43
    cZ
    cY
    eqcom
    cY
    cZ
    nne
    bitr4i
    orbi12i
    @9
    @10
    ianor
    sylbb2
    syl
    con2i
    3adant1
    3ad2ant3
    @13
    cZ
    disjsn
    sylibr
    @13
    @14
    @16
    @17
    @21
    @23
    fun
    syl21anc
    @29
    @26
    @27
    @24
    wf
    @25
    @26
    @27
    @28
    @24
    @19
    @20
    @22
    df-tp
    feq1i
    @26
    @27
    @15
    @18
    @24
    cX
    cY
    cZ
    df-tp
    cA
    cB
    cC
    df-tp
    feq23i
    bitri
    sylibr
end
