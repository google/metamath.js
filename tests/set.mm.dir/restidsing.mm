include "cid.mm"
include "csn.mm"
include "cres.mm"
include "cxp.mm"
include "relres.mm"
include "relxp.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wbr.mm"
include "velsn.mm"
include "anbi12i.mm"
include "weq.mm"
include "vex.mm"
include "ideq.mm"
include "ancom.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "3bitri.mm"
include "df-br.mm"
include "anbi1i.mm"
include "3bitr2ri.mm"
include "opelres.mm"
include "opelxp.mm"
include "3bitr4i.mm"
include "eqrelriiv.mm"

theorem restidsing
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( _I |` { A } ) = ( { A } X. { A } )

  proof
    vx
    vy
    cid
    cA
    csn
    #
    cres
    #
    @0
    @0
    cxp
    #
    cid
    @0
    relres
    @0
    @0
    relxp
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cid
    wcel
    #
    @3
    @0
    wcel
    #
    wa
    #
    @7
    @4
    @0
    wcel
    #
    wa
    #
    @5
    @1
    wcel
    @5
    @2
    wcel
    @10
    @3
    cA
    wceq
    #
    @4
    cA
    wceq
    #
    wa
    #
    @3
    @4
    cid
    wbr
    #
    @7
    wa
    #
    @8
    @7
    @11
    @9
    @12
    vx
    cA
    velsn
    #
    vy
    cA
    velsn
    anbi12i
    @15
    vx
    vy
    weq
    #
    @11
    wa
    @11
    @17
    wa
    @13
    @14
    @17
    @7
    @11
    @3
    @4
    vy
    vex
    #
    ideq
    @16
    anbi12i
    @17
    @11
    ancom
    @11
    @17
    @12
    @11
    @17
    cA
    @4
    wceq
    @12
    @3
    cA
    @4
    eqeq1
    cA
    @4
    eqcom
    syl6bb
    pm5.32i
    3bitri
    @14
    @6
    @7
    @3
    @4
    cid
    df-br
    anbi1i
    3bitr2ri
    @3
    @4
    cid
    @0
    @18
    opelres
    @3
    @4
    @0
    @0
    opelxp
    3bitr4i
    eqrelriiv
end
