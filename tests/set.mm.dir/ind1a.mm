include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cind.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "indfval.mm"
include "eqeq1d.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "eqid.mm"
include "biantru.mm"
include "ax-1ne0.mm"
include "neii.mm"
include "biorfi.mm"
include "bianfi.mm"
include "orbi2i.mm"
include "3bitri.mm"
include "eqif.mm"
include "eqcom.mm"
include "3bitr2ri.mm"
include "syl6bb.mm"

theorem ind1a
  let cA: class A
  let cO: class O
  let cV: class V
  let cX: class X


  assert |- ( ( O e. V /\ A C_ O /\ X e. O ) -> ( ( ( ( _Ind ` O ) ` A ) ` X ) = 1 <-> X e. A ) )

  proof
    cO
    cV
    wcel
    cA
    cO
    wss
    cX
    cO
    wcel
    w3a
    #
    cX
    cA
    cO
    cind
    cfv
    cfv
    cfv
    #
    c1
    wceq
    cX
    cA
    wcel
    #
    c1
    cc0
    cif
    #
    c1
    wceq
    #
    @2
    @0
    @1
    @3
    c1
    cA
    cO
    cV
    cX
    indfval
    eqeq1d
    @2
    @2
    c1
    c1
    wceq
    #
    wa
    #
    @2
    wn
    #
    c1
    cc0
    wceq
    #
    wa
    #
    wo
    #
    c1
    @3
    wceq
    @4
    @2
    @6
    @6
    @8
    wo
    @10
    @5
    @2
    c1
    eqid
    biantru
    @8
    @6
    c1
    cc0
    ax-1ne0
    neii
    #
    biorfi
    @8
    @9
    @6
    @8
    @7
    @11
    bianfi
    orbi2i
    3bitri
    @2
    c1
    c1
    cc0
    eqif
    c1
    @3
    eqcom
    3bitr2ri
    syl6bb
end
