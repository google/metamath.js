include "cvv.mm"
include "wcel.mm"
include "coc.mm"
include "cfv.mm"
include "wceq.mm"
include "ccss.mm"
include "cipo.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "eqid.mm"
include "thlval.mm"
include "fveq2d.mm"
include "fvex.mm"
include "cocv.mm"
include "eqeltri.mm"
include "ocid.mm"
include "setsid.mm"
include "mp2an.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "cthl.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem thloc
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let vh: setvar h
  let cI: class I
  assume thlval.k: |- K = ( toHL ` W )
  assume thloc.c: |- ._|_ = ( ocv ` W )


  assert |- ._|_ = ( oc ` K )

  proof
    cW
    cvv
    wcel
    #
    c.pe
    cK
    coc
    cfv
    #
    wceq
    @0
    @1
    cW
    ccss
    cfv
    #
    cipo
    cfv
    #
    cnx
    coc
    cfv
    #
    c.pe
    cop
    csts
    co
    #
    coc
    cfv
    #
    c.pe
    @0
    cK
    @5
    coc
    @2
    @3
    cK
    c.pe
    cvv
    cW
    thlval.k
    @2
    eqid
    @3
    eqid
    thloc.c
    thlval
    fveq2d
    @3
    cvv
    wcel
    c.pe
    cvv
    wcel
    c.pe
    @6
    wceq
    @2
    cipo
    fvex
    c.pe
    cW
    cocv
    cfv
    #
    cvv
    thloc.c
    cW
    cocv
    fvex
    eqeltri
    cvv
    c.pe
    coc
    cvv
    @3
    ocid
    setsid
    mp2an
    syl6reqr
    @0
    wn
    #
    c0
    c0
    coc
    cfv
    c.pe
    @1
    coc
    @4
    ocid
    str0
    @8
    c.pe
    @7
    c0
    thloc.c
    cW
    cocv
    fvprc
    syl5eq
    @8
    cK
    c0
    coc
    @8
    cK
    cW
    cthl
    cfv
    c0
    thlval.k
    cW
    cthl
    fvprc
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
end
