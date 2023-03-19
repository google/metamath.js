include "crngo.mm"
include "wcel.mm"
include "cmaxidl.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "cidl.mm"
include "wral.mm"
include "wa.mm"
include "crab.mm"
include "w3a.mm"
include "maxidlval.mm"
include "eleq2d.mm"
include "neeq1.mm"
include "sseq1.mm"
include "eqeq2.mm"
include "orbi1d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem ismaxidl
  let cR: class R
  let vj: setvar j
  let cG: class G
  let cM: class M
  let cX: class X
  let vi: setvar i
  assume ismaxidl.1: |- G = ( 1st ` R )
  assume ismaxidl.2: |- X = ran G

  disjoint R j
  disjoint M j
  disjoint R i
  disjoint i j
  disjoint M i
  disjoint X i
  assert |- ( R e. RingOps -> ( M e. ( MaxIdl ` R ) <-> ( M e. ( Idl ` R ) /\ M =/= X /\ A. j e. ( Idl ` R ) ( M C_ j -> ( j = M \/ j = X ) ) ) ) )

  proof
    cR
    crngo
    wcel
    #
    cM
    cR
    cmaxidl
    cfv
    #
    wcel
    cM
    vi
    cv
    #
    cX
    wne
    #
    @2
    vj
    cv
    #
    wss
    #
    @4
    @2
    wceq
    #
    @4
    cX
    wceq
    #
    wo
    #
    wi
    #
    vj
    cR
    cidl
    cfv
    #
    wral
    #
    wa
    #
    vi
    @10
    crab
    #
    wcel
    #
    cM
    @10
    wcel
    #
    cM
    cX
    wne
    #
    cM
    @4
    wss
    #
    @4
    cM
    wceq
    #
    @7
    wo
    #
    wi
    #
    vj
    @10
    wral
    #
    w3a
    #
    @0
    @1
    @13
    cM
    cR
    vi
    vj
    cG
    cX
    ismaxidl.1
    ismaxidl.2
    maxidlval
    eleq2d
    @14
    @15
    @16
    @21
    wa
    #
    wa
    @22
    @12
    @23
    vi
    cM
    @10
    @2
    cM
    wceq
    #
    @3
    @16
    @11
    @21
    @2
    cM
    cX
    neeq1
    @24
    @9
    @20
    vj
    @10
    @24
    @5
    @17
    @8
    @19
    @2
    cM
    @4
    sseq1
    @24
    @6
    @18
    @7
    @2
    cM
    @4
    eqeq2
    orbi1d
    imbi12d
    ralbidv
    anbi12d
    elrab
    @15
    @16
    @21
    3anass
    bitr4i
    syl6bb
end
