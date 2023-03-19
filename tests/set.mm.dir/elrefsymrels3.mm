include "crefrels.mm"
include "csymrels.mm"
include "cin.mm"
include "wcel.mm"
include "cid.mm"
include "cdm.mm"
include "cres.mm"
include "wss.mm"
include "ccnv.mm"
include "wa.mm"
include "crels.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "elrefsymrels2.mm"
include "issref.mm"
include "cnvsym.mm"
include "anbi12i.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem elrefsymrels3
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( R e. ( RefRels i^i SymRels ) <-> ( ( A. x e. dom R x R x /\ A. x A. y ( x R y -> y R x ) ) /\ R e. Rels ) )

  proof
    cR
    crefrels
    csymrels
    cin
    wcel
    cid
    cR
    cdm
    #
    cres
    cR
    wss
    #
    cR
    ccnv
    cR
    wss
    #
    wa
    #
    cR
    crels
    wcel
    #
    wa
    vx
    cv
    #
    @5
    cR
    wbr
    vx
    @0
    wral
    #
    @5
    vy
    cv
    #
    cR
    wbr
    @7
    @5
    cR
    wbr
    wi
    vy
    wal
    vx
    wal
    #
    wa
    #
    @4
    wa
    cR
    elrefsymrels2
    @3
    @9
    @4
    @1
    @6
    @2
    @8
    vx
    @0
    cR
    issref
    vx
    vy
    cR
    cnvsym
    anbi12i
    anbi1i
    bitri
end
