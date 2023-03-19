include "wcel.mm"
include "w3a.mm"
include "cvtx.mm"
include "cfv.mm"
include "ctp.mm"
include "wceq.mm"
include "cusgr.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "cpr.mm"
include "cedg.mm"
include "wi.mm"
include "prcom.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "adantl.mm"
include "anim12i.mm"
include "a1i.mm"
include "eqid.mm"
include "simprr.mm"
include "simprl.mm"
include "simpl.mm"
include "nb3grprlem1.mm"
include "wb.mm"
include "3ancoma.mm"
include "tpcoma.mm"
include "eqeq2i.mm"
include "anim1i.mm"
include "syl2an.mm"
include "anbi12d.mm"
include "3anrot.mm"
include "biimpri.mm"
include "tprot.mm"
include "eqcomi.mm"
include "anbi1i.mm"
include "3imtr4d.mm"
include "pm4.71d.mm"
include "df-3an.mm"
include "syl6bbr.mm"

theorem nb3gr2nb
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( ( ( A e. X /\ B e. Y /\ C e. Z ) /\ ( ( Vtx ` G ) = { A , B , C } /\ G e. USGraph ) ) -> ( ( ( G NeighbVtx A ) = { B , C } /\ ( G NeighbVtx B ) = { A , C } ) <-> ( ( G NeighbVtx A ) = { B , C } /\ ( G NeighbVtx B ) = { A , C } /\ ( G NeighbVtx C ) = { A , B } ) ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cC
    cZ
    wcel
    #
    w3a
    #
    cG
    cvtx
    cfv
    #
    cA
    cB
    cC
    ctp
    #
    wceq
    #
    cG
    cusgr
    wcel
    #
    wa
    #
    wa
    #
    cG
    cA
    cnbgr
    co
    cB
    cC
    cpr
    #
    wceq
    #
    cG
    cB
    cnbgr
    co
    cA
    cC
    cpr
    #
    wceq
    #
    wa
    #
    @14
    cG
    cC
    cnbgr
    co
    cA
    cB
    cpr
    #
    wceq
    #
    wa
    @11
    @13
    @16
    w3a
    @9
    @14
    @16
    @9
    @15
    cG
    cedg
    cfv
    #
    wcel
    #
    @12
    @17
    wcel
    #
    wa
    #
    cB
    cA
    cpr
    @17
    wcel
    #
    @10
    @17
    wcel
    #
    wa
    #
    wa
    #
    cC
    cA
    cpr
    #
    @17
    wcel
    #
    cC
    cB
    cpr
    #
    @17
    wcel
    #
    wa
    #
    @14
    @16
    @24
    @29
    wi
    @9
    @20
    @26
    @23
    @28
    @19
    @26
    @18
    @19
    @26
    @12
    @25
    @17
    cA
    cC
    prcom
    eleq1i
    biimpi
    adantl
    @22
    @28
    @21
    @22
    @28
    @10
    @27
    @17
    cB
    cC
    prcom
    eleq1i
    biimpi
    adantl
    anim12i
    a1i
    @9
    @11
    @20
    @13
    @23
    @9
    cA
    cB
    cC
    @17
    cG
    @4
    cX
    cY
    cZ
    @4
    eqid
    #
    @17
    eqid
    #
    @3
    @6
    @7
    simprr
    @3
    @6
    @7
    simprl
    @3
    @8
    simpl
    nb3grprlem1
    @3
    @1
    @0
    @2
    w3a
    #
    @4
    cB
    cA
    cC
    ctp
    #
    wceq
    #
    @7
    wa
    #
    @13
    @23
    wb
    @8
    @3
    @32
    @0
    @1
    @2
    3ancoma
    biimpi
    @6
    @34
    @7
    @6
    @34
    @5
    @33
    @4
    cA
    cB
    cC
    tpcoma
    eqeq2i
    biimpi
    anim1i
    @32
    @35
    wa
    cB
    cA
    cC
    @17
    cG
    @4
    cY
    cX
    cZ
    @30
    @31
    @32
    @34
    @7
    simprr
    @32
    @34
    @7
    simprl
    @32
    @35
    simpl
    nb3grprlem1
    syl2an
    anbi12d
    @3
    @2
    @0
    @1
    w3a
    #
    @4
    cC
    cA
    cB
    ctp
    #
    wceq
    #
    @7
    wa
    #
    @16
    @29
    wb
    @8
    @36
    @3
    @2
    @0
    @1
    3anrot
    biimpri
    @8
    @39
    @6
    @38
    @7
    @5
    @37
    @4
    @37
    @5
    cC
    cA
    cB
    tprot
    eqcomi
    eqeq2i
    anbi1i
    biimpi
    @36
    @39
    wa
    cC
    cA
    cB
    @17
    cG
    @4
    cZ
    cX
    cY
    @30
    @31
    @36
    @38
    @7
    simprr
    @36
    @38
    @7
    simprl
    @36
    @39
    simpl
    nb3grprlem1
    syl2an
    3imtr4d
    pm4.71d
    @11
    @13
    @16
    df-3an
    syl6bbr
end
