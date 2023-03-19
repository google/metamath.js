include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "cop.mm"
include "ctp.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "funtpg.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "wa.mm"
include "dmsnopg.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "jca.mm"
include "uneq12.mm"
include "syl.mm"
include "df-pr.mm"
include "syl6eqr.mm"
include "dmeqi.mm"
include "eqeq1i.mm"
include "dmun.mm"
include "bitri.mm"
include "sylibr.mm"
include "3ad2ant3.mm"
include "uneq12d.mm"
include "df-tp.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "df-fn.mm"
include "sylanbrc.mm"

theorem fntpg
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


  assert |- ( ( ( X e. U /\ Y e. V /\ Z e. W ) /\ ( A e. F /\ B e. G /\ C e. H ) /\ ( X =/= Y /\ X =/= Z /\ Y =/= Z ) ) -> { <. X , A >. , <. Y , B >. , <. Z , C >. } Fn { X , Y , Z } )

  proof
    cX
    cU
    wcel
    cY
    cV
    wcel
    cZ
    cW
    wcel
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
    cX
    cZ
    wne
    cY
    cZ
    wne
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
    cZ
    cC
    cop
    #
    ctp
    #
    wfun
    @10
    cdm
    #
    cX
    cY
    cZ
    ctp
    #
    wceq
    @10
    @12
    wfn
    cA
    cB
    cC
    cU
    cF
    cG
    cH
    cV
    cW
    cX
    cY
    cZ
    funtpg
    @6
    @7
    @8
    cpr
    #
    cdm
    #
    @9
    csn
    #
    cdm
    #
    cun
    #
    cX
    cY
    cpr
    #
    cZ
    csn
    #
    cun
    @11
    @12
    @6
    @14
    @18
    @16
    @19
    @6
    @7
    csn
    #
    cdm
    #
    @8
    csn
    #
    cdm
    #
    cun
    #
    @18
    wceq
    #
    @14
    @18
    wceq
    #
    @6
    @24
    cX
    csn
    #
    cY
    csn
    #
    cun
    #
    @18
    @6
    @21
    @27
    wceq
    #
    @23
    @28
    wceq
    #
    wa
    #
    @24
    @29
    wceq
    @4
    @0
    @32
    @5
    @4
    @30
    @31
    @1
    @2
    @30
    @3
    cX
    cA
    cF
    dmsnopg
    3ad2ant1
    @2
    @1
    @31
    @3
    cY
    cB
    cG
    dmsnopg
    3ad2ant2
    jca
    3ad2ant2
    @21
    @27
    @23
    @28
    uneq12
    syl
    cX
    cY
    df-pr
    syl6eqr
    @26
    @20
    @22
    cun
    #
    cdm
    #
    @18
    wceq
    @25
    @14
    @34
    @18
    @13
    @33
    @7
    @8
    df-pr
    dmeqi
    eqeq1i
    @34
    @24
    @18
    @20
    @22
    dmun
    eqeq1i
    bitri
    sylibr
    @4
    @0
    @16
    @19
    wceq
    #
    @5
    @3
    @1
    @35
    @2
    cZ
    cC
    cH
    dmsnopg
    3ad2ant3
    3ad2ant2
    uneq12d
    @11
    @13
    @15
    cun
    #
    cdm
    @17
    @10
    @36
    @7
    @8
    @9
    df-tp
    dmeqi
    @13
    @15
    dmun
    eqtri
    cX
    cY
    cZ
    df-tp
    3eqtr4g
    @10
    @12
    df-fn
    sylanbrc
end
