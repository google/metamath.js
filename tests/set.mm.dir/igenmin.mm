include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "cigen.mm"
include "co.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "c1st.mm"
include "crn.mm"
include "eqid.mm"
include "idlss.mm"
include "wa.mm"
include "sstr.mm"
include "ancoms.mm"
include "igenval.mm"
include "sylan2.mm"
include "anassrs.mm"
include "syldanl.mm"
include "3impa.mm"
include "sseq2.mm"
include "intminss.mm"
include "3adant1.mm"
include "eqsstrd.mm"

theorem igenmin
  let cR: class R
  let cS: class S
  let cI: class I
  let vj: setvar j


  assert |- ( ( R e. RingOps /\ I e. ( Idl ` R ) /\ S C_ I ) -> ( R IdlGen S ) C_ I )

  proof
    cR
    crngo
    wcel
    #
    cI
    cR
    cidl
    cfv
    #
    wcel
    #
    cS
    cI
    wss
    #
    w3a
    cR
    cS
    cigen
    co
    #
    cS
    vj
    cv
    #
    wss
    #
    vj
    @1
    crab
    cint
    #
    cI
    @0
    @2
    @3
    @4
    @7
    wceq
    #
    @0
    @2
    cI
    cR
    c1st
    cfv
    #
    crn
    #
    wss
    #
    @3
    @8
    cR
    @9
    cI
    @10
    @9
    eqid
    #
    @10
    eqid
    #
    idlss
    @0
    @11
    @3
    @8
    @11
    @3
    wa
    @0
    cS
    @10
    wss
    #
    @8
    @3
    @11
    @14
    cS
    cI
    @10
    sstr
    ancoms
    cR
    cS
    vj
    @9
    @10
    @12
    @13
    igenval
    sylan2
    anassrs
    syldanl
    3impa
    @2
    @3
    @7
    cI
    wss
    @0
    @6
    @3
    vj
    cI
    @1
    @5
    cI
    cS
    sseq2
    intminss
    3adant1
    eqsstrd
end
