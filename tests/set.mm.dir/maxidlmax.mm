include "crngo.mm"
include "wcel.mm"
include "cmaxidl.mm"
include "cfv.mm"
include "wa.mm"
include "cidl.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "wne.mm"
include "w3a.mm"
include "ismaxidl.mm"
include "biimpa.mm"
include "simp3d.mm"
include "sseq2.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "sylan2.mm"
include "ancoms.mm"
include "impr.mm"

theorem maxidlmax
  let cR: class R
  let cG: class G
  let cI: class I
  let cM: class M
  let cX: class X
  let vj: setvar j
  assume maxidlnr.1: |- G = ( 1st ` R )
  assume maxidlnr.2: |- X = ran G


  assert |- ( ( ( R e. RingOps /\ M e. ( MaxIdl ` R ) ) /\ ( I e. ( Idl ` R ) /\ M C_ I ) ) -> ( I = M \/ I = X ) )

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
    #
    cI
    cR
    cidl
    cfv
    #
    wcel
    #
    cM
    cI
    wss
    #
    cI
    cM
    wceq
    #
    cI
    cX
    wceq
    #
    wo
    #
    @4
    @2
    @5
    @8
    wi
    #
    @2
    @4
    cM
    vj
    cv
    #
    wss
    #
    @10
    cM
    wceq
    #
    @10
    cX
    wceq
    #
    wo
    #
    wi
    #
    vj
    @3
    wral
    #
    @9
    @2
    cM
    @3
    wcel
    #
    cM
    cX
    wne
    #
    @16
    @0
    @1
    @17
    @18
    @16
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
    simp3d
    @15
    @9
    vj
    cI
    @3
    @10
    cI
    wceq
    #
    @11
    @5
    @14
    @8
    @10
    cI
    cM
    sseq2
    @19
    @12
    @6
    @13
    @7
    @10
    cI
    cM
    eqeq1
    @10
    cI
    cX
    eqeq1
    orbi12d
    imbi12d
    rspcva
    sylan2
    ancoms
    impr
end
