include "crefrels.mm"
include "csymrels.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "wrefrel.mm"
include "wsymrel.mm"
include "elin.mm"
include "elrefrelsrel.mm"
include "elsymrelsrel.mm"
include "anbi12d.mm"
include "syl5bb.mm"

theorem elrefsymrelsrel
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R e. ( RefRels i^i SymRels ) <-> ( RefRel R /\ SymRel R ) ) )

  proof
    cR
    crefrels
    csymrels
    cin
    wcel
    cR
    crefrels
    wcel
    #
    cR
    csymrels
    wcel
    #
    wa
    cR
    cV
    wcel
    #
    cR
    wrefrel
    #
    cR
    wsymrel
    #
    wa
    cR
    crefrels
    csymrels
    elin
    @2
    @0
    @3
    @1
    @4
    cR
    cV
    elrefrelsrel
    cR
    cV
    elsymrelsrel
    anbi12d
    syl5bb
end
