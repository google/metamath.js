include "cgrp.mm"
include "ctmd.mm"
include "cin.mm"
include "wcel.mm"
include "ccn.mm"
include "co.mm"
include "wa.mm"
include "ctgp.mm"
include "w3a.mm"
include "elin.mm"
include "anbi1i.mm"
include "cv.mm"
include "cminusg.mm"
include "cfv.mm"
include "ctopn.mm"
include "wsbc.mm"
include "wceq.mm"
include "cvv.mm"
include "fvexd.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "id.mm"
include "fveq2.mm"
include "sylan9eqr.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "sbcied.mm"
include "df-tgp.mm"
include "elrab2.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem istgp
  let cG: class G
  let cI: class I
  let cJ: class J
  let vf: setvar f
  let vj: setvar j
  assume istgp.1: |- J = ( TopOpen ` G )
  assume istgp.2: |- I = ( invg ` G )


  assert |- ( G e. TopGrp <-> ( G e. Grp /\ G e. TopMnd /\ I e. ( J Cn J ) ) )

  proof
    cG
    cgrp
    ctmd
    cin
    #
    wcel
    #
    cI
    cJ
    cJ
    ccn
    co
    #
    wcel
    #
    wa
    cG
    cgrp
    wcel
    #
    cG
    ctmd
    wcel
    #
    wa
    #
    @3
    wa
    cG
    ctgp
    wcel
    @4
    @5
    @3
    w3a
    @1
    @6
    @3
    cG
    cgrp
    ctmd
    elin
    anbi1i
    vf
    cv
    #
    cminusg
    cfv
    #
    vj
    cv
    #
    @9
    ccn
    co
    #
    wcel
    #
    vj
    @7
    ctopn
    cfv
    #
    wsbc
    @3
    vf
    cG
    @0
    ctgp
    @7
    cG
    wceq
    #
    @11
    @3
    vj
    @12
    cvv
    @13
    @7
    ctopn
    fvexd
    @13
    @9
    @12
    wceq
    #
    wa
    #
    @8
    cI
    @10
    @2
    @15
    @8
    cG
    cminusg
    cfv
    cI
    @15
    @7
    cG
    cminusg
    @13
    @14
    simpl
    fveq2d
    istgp.2
    syl6eqr
    @15
    @9
    cJ
    @9
    cJ
    ccn
    @14
    @13
    @9
    @12
    cJ
    @14
    id
    @13
    @12
    cG
    ctopn
    cfv
    cJ
    @7
    cG
    ctopn
    fveq2
    istgp.1
    syl6eqr
    sylan9eqr
    #
    @16
    oveq12d
    eleq12d
    sbcied
    vf
    vj
    df-tgp
    elrab2
    @4
    @5
    @3
    df-3an
    3bitr4i
end
