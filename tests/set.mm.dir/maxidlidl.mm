include "crngo.mm"
include "wcel.mm"
include "cmaxidl.mm"
include "cfv.mm"
include "cidl.mm"
include "c1st.mm"
include "crn.mm"
include "wne.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "eqid.mm"
include "ismaxidl.mm"
include "3anass.mm"
include "syl6bb.mm"
include "simprbda.mm"

theorem maxidlidl
  let cR: class R
  let cM: class M
  let vj: setvar j


  assert |- ( ( R e. RingOps /\ M e. ( MaxIdl ` R ) ) -> M e. ( Idl ` R ) )

  proof
    cR
    crngo
    wcel
    #
    cM
    cR
    cmaxidl
    cfv
    wcel
    #
    cM
    cR
    cidl
    cfv
    #
    wcel
    #
    cM
    cR
    c1st
    cfv
    #
    crn
    #
    wne
    #
    cM
    vj
    cv
    #
    wss
    @7
    cM
    wceq
    @7
    @5
    wceq
    wo
    wi
    vj
    @2
    wral
    #
    wa
    #
    @0
    @1
    @3
    @6
    @8
    w3a
    @3
    @9
    wa
    cR
    vj
    @4
    cM
    @5
    @4
    eqid
    @5
    eqid
    ismaxidl
    @3
    @6
    @8
    3anass
    syl6bb
    simprbda
end
