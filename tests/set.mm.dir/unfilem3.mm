include "com.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "cdif.mm"
include "cen.mm"
include "wbr.mm"
include "c0.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "id.mm"
include "difeq12d.mm"
include "breq2d.mm"
include "oveq2.mm"
include "difeq1d.mm"
include "breq12d.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "wf1o.mm"
include "peano1.mm"
include "elimel.mm"
include "ovex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "eqid.mm"
include "unfilem2.mm"
include "f1oen2g.mm"
include "mp3an.mm"
include "dedth2h.mm"

theorem unfilem3
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. _om /\ B e. _om ) -> B ~~ ( ( A +o B ) \ A ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    cB
    cA
    cB
    coa
    co
    #
    cA
    cdif
    #
    cen
    wbr
    cB
    @0
    cA
    c0
    cif
    #
    cB
    coa
    co
    #
    @4
    cdif
    #
    cen
    wbr
    @1
    cB
    c0
    cif
    #
    @4
    @7
    coa
    co
    #
    @4
    cdif
    #
    cen
    wbr
    #
    cA
    cB
    c0
    c0
    cA
    @4
    wceq
    #
    @3
    @6
    cB
    cen
    @11
    @2
    @5
    cA
    @4
    cA
    @4
    cB
    coa
    oveq1
    @11
    id
    difeq12d
    breq2d
    cB
    @7
    wceq
    #
    cB
    @7
    @6
    @9
    cen
    @12
    id
    @12
    @5
    @8
    @4
    cB
    @7
    @4
    coa
    oveq2
    difeq1d
    breq12d
    @7
    com
    wcel
    @9
    cvv
    wcel
    #
    @7
    @9
    vx
    @7
    @4
    vx
    cv
    coa
    co
    cmpt
    #
    wf1o
    @10
    cB
    c0
    com
    peano1
    elimel
    #
    @8
    cvv
    wcel
    @13
    @4
    @7
    coa
    ovex
    @8
    @4
    cvv
    difexg
    ax-mp
    vx
    @4
    @7
    @14
    cA
    c0
    com
    peano1
    elimel
    @15
    @14
    eqid
    unfilem2
    @7
    @9
    @14
    com
    cvv
    f1oen2g
    mp3an
    dedth2h
end
