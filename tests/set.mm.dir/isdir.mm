include "cv.mm"
include "wrel.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "wss.mm"
include "wa.mm"
include "ccom.mm"
include "cxp.mm"
include "ccnv.mm"
include "cdir.mm"
include "wceq.mm"
include "releq.mm"
include "unieq.mm"
include "unieqd.mm"
include "syl6eqr.mm"
include "reseq2d.mm"
include "id.mm"
include "sseq12d.mm"
include "anbi12d.mm"
include "coeq12d.mm"
include "sqxpeqd.mm"
include "cnveq.mm"
include "df-dir.mm"
include "elab2g.mm"

theorem isdir
  let cA: class A
  let cR: class R
  let cV: class V
  let vr: setvar r
  assume isdir.1: |- A = U. U. R


  assert |- ( R e. V -> ( R e. DirRel <-> ( ( Rel R /\ ( _I |` A ) C_ R ) /\ ( ( R o. R ) C_ R /\ ( A X. A ) C_ ( `' R o. R ) ) ) ) )

  proof
    vr
    cv
    #
    wrel
    #
    cid
    @0
    cuni
    #
    cuni
    #
    cres
    #
    @0
    wss
    #
    wa
    #
    @0
    @0
    ccom
    #
    @0
    wss
    #
    @3
    @3
    cxp
    #
    @0
    ccnv
    #
    @0
    ccom
    #
    wss
    #
    wa
    #
    wa
    cR
    wrel
    #
    cid
    cA
    cres
    #
    cR
    wss
    #
    wa
    #
    cR
    cR
    ccom
    #
    cR
    wss
    #
    cA
    cA
    cxp
    #
    cR
    ccnv
    #
    cR
    ccom
    #
    wss
    #
    wa
    #
    wa
    vr
    cR
    cdir
    cV
    @0
    cR
    wceq
    #
    @6
    @17
    @13
    @24
    @25
    @1
    @14
    @5
    @16
    @0
    cR
    releq
    @25
    @4
    @15
    @0
    cR
    @25
    @3
    cA
    cid
    @25
    @3
    cR
    cuni
    #
    cuni
    cA
    @25
    @2
    @26
    @0
    cR
    unieq
    unieqd
    isdir.1
    syl6eqr
    #
    reseq2d
    @25
    id
    #
    sseq12d
    anbi12d
    @25
    @8
    @19
    @12
    @23
    @25
    @7
    @18
    @0
    cR
    @25
    @0
    cR
    @0
    cR
    @28
    @28
    coeq12d
    @28
    sseq12d
    @25
    @9
    @20
    @11
    @22
    @25
    @3
    cA
    @27
    sqxpeqd
    @25
    @10
    @21
    @0
    cR
    @0
    cR
    cnveq
    @28
    coeq12d
    sseq12d
    anbi12d
    anbi12d
    vr
    df-dir
    elab2g
end
