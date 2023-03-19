include "wcel.mm"
include "cvv.mm"
include "cnx.mm"
include "coc.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "wceq.mm"
include "elex.mm"
include "cthl.mm"
include "cv.mm"
include "ccss.mm"
include "cipo.mm"
include "cocv.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "df-thl.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem thlval
  let cC: class C
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  assume thlval.k: |- K = ( toHL ` W )
  assume thlval.c: |- C = ( CSubSp ` W )
  assume thlval.i: |- I = ( toInc ` C )
  assume thlval.o: |- ._|_ = ( ocv ` W )


  assert |- ( W e. V -> K = ( I sSet <. ( oc ` ndx ) , ._|_ >. ) )

  proof
    cW
    cV
    wcel
    cW
    cvv
    wcel
    #
    cK
    cI
    cnx
    coc
    cfv
    #
    c.pe
    cop
    #
    csts
    co
    #
    wceq
    cW
    cV
    elex
    @0
    cK
    cW
    cthl
    cfv
    @3
    thlval.k
    vh
    cW
    vh
    cv
    #
    ccss
    cfv
    #
    cipo
    cfv
    #
    @1
    @4
    cocv
    cfv
    #
    cop
    #
    csts
    co
    @3
    cvv
    cthl
    @4
    cW
    wceq
    #
    @6
    cI
    @8
    @2
    csts
    @9
    @6
    cC
    cipo
    cfv
    cI
    @9
    @5
    cC
    cipo
    @9
    @5
    cW
    ccss
    cfv
    cC
    @4
    cW
    ccss
    fveq2
    thlval.c
    syl6eqr
    fveq2d
    thlval.i
    syl6eqr
    @9
    @7
    c.pe
    @1
    @9
    @7
    cW
    cocv
    cfv
    c.pe
    @4
    cW
    cocv
    fveq2
    thlval.o
    syl6eqr
    opeq2d
    oveq12d
    vh
    df-thl
    cI
    @2
    csts
    ovex
    fvmpt
    syl5eq
    syl
end
