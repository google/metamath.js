include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "cab.mm"
include "cop.mm"
include "csn.mm"
include "symgbas.mm"
include "wceq.mm"
include "wb.mm"
include "eqidd.mm"
include "id.mm"
include "f1oeq123d.mm"
include "ax-mp.mm"
include "wf.mm"
include "f1of.mm"
include "fsng.mm"
include "anidms.mm"
include "syl5ib.mm"
include "f1osng.mm"
include "f1oeq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "syl5bb.mm"
include "vex.mm"
include "elab.mm"
include "velsn.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "syl5eq.mm"

theorem symg1bas
  let cA: class A
  let cB: class B
  let cG: class G
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vp: setvar p
  assume symg1bas.1: |- G = ( SymGrp ` A )
  assume symg1bas.2: |- B = ( Base ` G )
  assume symg1bas.0: |- A = { I }


  assert |- ( I e. V -> B = { { <. I , I >. } } )

  proof
    cI
    cV
    wcel
    #
    cB
    cA
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    cab
    #
    cI
    cI
    cop
    csn
    #
    csn
    #
    vf
    cA
    cB
    cG
    symg1bas.1
    symg1bas.2
    symgbas
    @0
    vp
    @3
    @5
    @0
    cA
    cA
    vp
    cv
    #
    wf1o
    #
    @6
    @4
    wceq
    #
    @6
    @3
    wcel
    @6
    @5
    wcel
    @7
    cI
    csn
    #
    @9
    @6
    wf1o
    #
    @0
    @8
    cA
    @9
    wceq
    #
    @7
    @10
    wb
    symg1bas.0
    @11
    cA
    @9
    cA
    @9
    @6
    @6
    @11
    @6
    eqidd
    @11
    id
    #
    @12
    f1oeq123d
    ax-mp
    @0
    @10
    @8
    @10
    @9
    @9
    @6
    wf
    #
    @0
    @8
    @9
    @9
    @6
    f1of
    @0
    @13
    @8
    wb
    cI
    cI
    cV
    cV
    @6
    fsng
    anidms
    syl5ib
    @0
    @10
    @8
    @9
    @9
    @4
    wf1o
    #
    @0
    @14
    cI
    cI
    cV
    cV
    f1osng
    anidms
    @9
    @9
    @6
    @4
    f1oeq1
    syl5ibrcom
    impbid
    syl5bb
    @2
    @7
    vf
    @6
    vp
    vex
    cA
    cA
    @1
    @6
    f1oeq1
    elab
    vp
    @4
    velsn
    3bitr4g
    eqrdv
    syl5eq
end
