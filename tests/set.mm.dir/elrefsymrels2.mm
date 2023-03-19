include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "cres.mm"
include "wss.mm"
include "ccnv.mm"
include "wa.mm"
include "crels.mm"
include "crefrels.mm"
include "csymrels.mm"
include "cin.mm"
include "refsymrels2.mm"
include "wceq.mm"
include "dmeq.mm"
include "reseq2d.mm"
include "id.mm"
include "sseq12d.mm"
include "cnveq.mm"
include "anbi12d.mm"
include "rabeqel.mm"

theorem elrefsymrels2
  let cR: class R
  let vr: setvar r


  assert |- ( R e. ( RefRels i^i SymRels ) <-> ( ( ( _I |` dom R ) C_ R /\ `' R C_ R ) /\ R e. Rels ) )

  proof
    cid
    vr
    cv
    #
    cdm
    #
    cres
    #
    @0
    wss
    #
    @0
    ccnv
    #
    @0
    wss
    #
    wa
    cid
    cR
    cdm
    #
    cres
    #
    cR
    wss
    #
    cR
    ccnv
    #
    cR
    wss
    #
    wa
    vr
    crels
    crefrels
    csymrels
    cin
    cR
    vr
    refsymrels2
    @0
    cR
    wceq
    #
    @3
    @8
    @5
    @10
    @11
    @2
    @7
    @0
    cR
    @11
    @1
    @6
    cid
    @0
    cR
    dmeq
    reseq2d
    @11
    id
    #
    sseq12d
    @11
    @4
    @9
    @0
    cR
    @0
    cR
    cnveq
    @12
    sseq12d
    anbi12d
    rabeqel
end
