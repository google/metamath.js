include "crg.mm"
include "wcel.mm"
include "cui.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "wa.mm"
include "cdr.mm"
include "opprringb.mm"
include "anbi1i.mm"
include "eqid.mm"
include "isdrng.mm"
include "opprbas.mm"
include "opprunit.mm"
include "oppr0.mm"
include "3bitr4i.mm"

theorem opprdrng
  let cR: class R
  let cO: class O
  assume opprdrng.1: |- O = ( oppR ` R )


  assert |- ( R e. DivRing <-> O e. DivRing )

  proof
    cR
    crg
    wcel
    #
    cR
    cui
    cfv
    #
    cR
    cbs
    cfv
    #
    cR
    c0g
    cfv
    #
    csn
    cdif
    wceq
    #
    wa
    cO
    crg
    wcel
    #
    @4
    wa
    cR
    cdr
    wcel
    cO
    cdr
    wcel
    @0
    @5
    @4
    cR
    cO
    opprdrng.1
    opprringb
    anbi1i
    @2
    cR
    @1
    @3
    @2
    eqid
    #
    @1
    eqid
    #
    @3
    eqid
    #
    isdrng
    @2
    cO
    @1
    @3
    @2
    cR
    cO
    opprdrng.1
    @6
    opprbas
    cR
    cO
    @1
    @7
    opprdrng.1
    opprunit
    cR
    cO
    @3
    opprdrng.1
    @8
    oppr0
    isdrng
    3bitr4i
end
