include "wcel.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "wss.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cin.mm"
include "cop.mm"
include "csts.mm"
include "cif.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "simpl.mm"
include "ovex.mm"
include "ifcl.mm"
include "sylancl.mm"
include "cv.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "simpr.mm"
include "sseq12d.mm"
include "ineq12d.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "ifbieq12d.mm"
include "df-ress.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"
include "syl2an.mm"
include "syl5eq.mm"

theorem ressval
  let cA: class A
  let cB: class B
  let cR: class R
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vw: setvar w
  assume ressbas.r: |- R = ( W |`s A )
  assume ressbas.b: |- B = ( Base ` W )


  assert |- ( ( W e. X /\ A e. Y ) -> R = if ( B C_ A , W , ( W sSet <. ( Base ` ndx ) , ( A i^i B ) >. ) ) )

  proof
    cW
    cX
    wcel
    #
    cA
    cY
    wcel
    #
    wa
    cR
    cW
    cA
    cress
    co
    #
    cB
    cA
    wss
    #
    cW
    cW
    cnx
    cbs
    cfv
    #
    cA
    cB
    cin
    #
    cop
    #
    csts
    co
    #
    cif
    #
    ressbas.r
    @0
    cW
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @2
    @8
    wceq
    #
    @1
    cW
    cX
    elex
    cA
    cY
    elex
    @9
    @10
    @8
    cvv
    wcel
    #
    @11
    @9
    @10
    wa
    @9
    @7
    cvv
    wcel
    @12
    @9
    @10
    simpl
    cW
    @6
    csts
    ovex
    @3
    cW
    @7
    cvv
    ifcl
    sylancl
    vw
    va
    cW
    cA
    cvv
    cvv
    vw
    cv
    #
    cbs
    cfv
    #
    va
    cv
    #
    wss
    #
    @13
    @13
    @4
    @15
    @14
    cin
    #
    cop
    #
    csts
    co
    #
    cif
    @8
    cress
    cvv
    @13
    cW
    wceq
    #
    @15
    cA
    wceq
    #
    wa
    #
    @16
    @3
    @13
    @19
    cW
    @7
    @22
    @14
    cB
    @15
    cA
    @22
    @14
    cW
    cbs
    cfv
    cB
    @22
    @13
    cW
    cbs
    @20
    @21
    simpl
    #
    fveq2d
    ressbas.b
    syl6eqr
    #
    @20
    @21
    simpr
    #
    sseq12d
    @23
    @22
    @13
    cW
    @18
    @6
    csts
    @23
    @22
    @17
    @5
    @4
    @22
    @15
    cA
    @14
    cB
    @25
    @24
    ineq12d
    opeq2d
    oveq12d
    ifbieq12d
    va
    vw
    df-ress
    ovmpt2ga
    mpd3an3
    syl2an
    syl5eq
end
