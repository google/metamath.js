include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "wcel.mm"
include "wxo.mm"
include "wf1o.mm"
include "cvv.mm"
include "csn.mm"
include "wss.mm"
include "ccom.mm"
include "wb.mm"
include "wn.mm"
include "notbi.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjsn.mm"
include "disj2.mm"
include "bitr3i.mm"
include "bibi12i.mm"
include "bitri.mm"
include "notbii.mm"
include "df-xor.mm"
include "3bitr4i.mm"
include "w3a.mm"
include "f1omvdco2.mm"
include "con2bii.mm"
include "sylibr.mm"
include "syl3an3b.mm"

theorem f1omvdco3
  let cA: class A
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F : A -1-1-onto-> A /\ G : A -1-1-onto-> A /\ ( X e. dom ( F \ _I ) \/_ X e. dom ( G \ _I ) ) ) -> X e. dom ( ( F o. G ) \ _I ) )

  proof
    cX
    cF
    cid
    cdif
    cdm
    #
    wcel
    #
    cX
    cG
    cid
    cdif
    cdm
    #
    wcel
    #
    wxo
    #
    cA
    cA
    cF
    wf1o
    #
    cA
    cA
    cG
    wf1o
    #
    @0
    cvv
    cX
    csn
    #
    cdif
    #
    wss
    #
    @2
    @8
    wss
    #
    wxo
    #
    cX
    cF
    cG
    ccom
    cid
    cdif
    cdm
    #
    wcel
    #
    @1
    @3
    wb
    #
    wn
    @9
    @10
    wb
    #
    wn
    @4
    @11
    @14
    @15
    @14
    @1
    wn
    #
    @3
    wn
    #
    wb
    @15
    @1
    @3
    notbi
    @16
    @9
    @17
    @10
    @16
    @0
    @7
    cin
    c0
    wceq
    @9
    @0
    cX
    disjsn
    @0
    @7
    disj2
    bitr3i
    @17
    @2
    @7
    cin
    c0
    wceq
    @10
    @2
    cX
    disjsn
    @2
    @7
    disj2
    bitr3i
    bibi12i
    bitri
    notbii
    @1
    @3
    df-xor
    @9
    @10
    df-xor
    3bitr4i
    @5
    @6
    @11
    w3a
    @12
    @8
    wss
    #
    wn
    @13
    cA
    cF
    cG
    @8
    f1omvdco2
    @18
    @13
    @18
    @12
    @7
    cin
    c0
    wceq
    @13
    wn
    @12
    @7
    disj2
    @12
    cX
    disjsn
    bitr3i
    con2bii
    sylibr
    syl3an3b
end
