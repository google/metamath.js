include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wa.mm"
include "cigen.mm"
include "co.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "c1st.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "idlss.mm"
include "igenval.mm"
include "syldan.mm"
include "intmin.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem igenidl2
  let cR: class R
  let cI: class I
  let vj: setvar j
  let cS: class S


  assert |- ( ( R e. RingOps /\ I e. ( Idl ` R ) ) -> ( R IdlGen I ) = I )

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
    wa
    cR
    cI
    cigen
    co
    #
    cI
    vj
    cv
    wss
    vj
    @1
    crab
    cint
    #
    cI
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
    @3
    @4
    wceq
    cR
    @5
    cI
    @6
    @5
    eqid
    #
    @6
    eqid
    #
    idlss
    cR
    cI
    vj
    @5
    @6
    @7
    @8
    igenval
    syldan
    @2
    @4
    cI
    wceq
    @0
    vj
    cI
    @1
    intmin
    adantl
    eqtrd
end
