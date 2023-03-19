include "wfn.mm"
include "wss.mm"
include "w3a.mm"
include "cres.mm"
include "wceq.mm"
include "cin.mm"
include "cdm.mm"
include "wb.mm"
include "fnssres.mm"
include "3adant2.mm"
include "3adant1.mm"
include "fneqeql.mm"
include "syl2anc.mm"
include "resindir.mm"
include "dmeqi.mm"
include "dmres.mm"
include "eqtr3i.mm"
include "eqeq1i.mm"
include "df-ss.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem fnreseql
  let cA: class A
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x


  assert |- ( ( F Fn A /\ G Fn A /\ X C_ A ) -> ( ( F |` X ) = ( G |` X ) <-> X C_ dom ( F i^i G ) ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cA
    wfn
    #
    cX
    cA
    wss
    #
    w3a
    #
    cF
    cX
    cres
    #
    cG
    cX
    cres
    #
    wceq
    #
    @4
    @5
    cin
    #
    cdm
    #
    cX
    wceq
    #
    cX
    cF
    cG
    cin
    #
    cdm
    #
    wss
    #
    @3
    @4
    cX
    wfn
    #
    @5
    cX
    wfn
    #
    @6
    @9
    wb
    @0
    @2
    @13
    @1
    cA
    cX
    cF
    fnssres
    3adant2
    @1
    @2
    @14
    @0
    cA
    cX
    cG
    fnssres
    3adant1
    cX
    @4
    @5
    fneqeql
    syl2anc
    @9
    cX
    @11
    cin
    #
    cX
    wceq
    @12
    @8
    @15
    cX
    @10
    cX
    cres
    #
    cdm
    @8
    @15
    @16
    @7
    cF
    cG
    cX
    resindir
    dmeqi
    @10
    cX
    dmres
    eqtr3i
    eqeq1i
    cX
    @11
    df-ss
    bitr4i
    syl6bb
end
