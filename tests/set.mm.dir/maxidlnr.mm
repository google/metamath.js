include "crngo.mm"
include "wcel.mm"
include "cmaxidl.mm"
include "cfv.mm"
include "wa.mm"
include "cidl.mm"
include "wne.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "ismaxidl.mm"
include "biimpa.mm"
include "simp2d.mm"

theorem maxidlnr
  let cR: class R
  let cG: class G
  let cM: class M
  let cX: class X
  let vj: setvar j
  assume maxidlnr.1: |- G = ( 1st ` R )
  assume maxidlnr.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ M e. ( MaxIdl ` R ) ) -> M =/= X )

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
    wa
    cM
    cR
    cidl
    cfv
    #
    wcel
    #
    cM
    cX
    wne
    #
    cM
    vj
    cv
    #
    wss
    @5
    cM
    wceq
    @5
    cX
    wceq
    wo
    wi
    vj
    @2
    wral
    #
    @0
    @1
    @3
    @4
    @6
    w3a
    cR
    vj
    cG
    cM
    cX
    maxidlnr.1
    maxidlnr.2
    ismaxidl
    biimpa
    simp2d
end
