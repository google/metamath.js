include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "cres.mm"
include "wss.mm"
include "ccnv.mm"
include "wa.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wal.mm"
include "crels.mm"
include "crefrels.mm"
include "csymrels.mm"
include "cin.mm"
include "refsymrels2.mm"
include "issref.mm"
include "cnvsym.mm"
include "anbi12i.mm"
include "rabbieq.mm"

theorem refsymrels3
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r

  disjoint r x
  disjoint r y
  disjoint x y
  assert |- ( RefRels i^i SymRels ) = { r e. Rels | ( A. x e. dom r x r x /\ A. x A. y ( x r y -> y r x ) ) }

  proof
    cid
    vr
    cv
    #
    cdm
    #
    cres
    @0
    wss
    #
    @0
    ccnv
    @0
    wss
    #
    wa
    vx
    cv
    #
    @4
    @0
    wbr
    vx
    @1
    wral
    #
    @4
    vy
    cv
    #
    @0
    wbr
    @6
    @4
    @0
    wbr
    wi
    vy
    wal
    vx
    wal
    #
    wa
    vr
    crels
    crefrels
    csymrels
    cin
    vr
    refsymrels2
    @2
    @5
    @3
    @7
    vx
    @1
    @0
    issref
    vx
    vy
    @0
    cnvsym
    anbi12i
    rabbieq
end
