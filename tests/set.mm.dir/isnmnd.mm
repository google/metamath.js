include "cv.mm"
include "co.mm"
include "wne.mm"
include "wrex.mm"
include "wral.mm"
include "cmnd.mm"
include "wcel.mm"
include "wn.mm"
include "wnel.mm"
include "csgrp.mm"
include "wceq.mm"
include "wa.mm"
include "neneq.mm"
include "intnanrd.mm"
include "reximi.mm"
include "ralimi.mm"
include "rexnal.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "sylib.mm"
include "intnand.mm"
include "ismnddef.mm"
include "sylnibr.mm"
include "df-nel.mm"
include "sylibr.mm"

theorem isnmnd
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let cM: class M
  let c.op: class .o.
  assume isnmnd.b: |- B = ( Base ` M )
  assume isnmnd.o: |- .o. = ( +g ` M )

  disjoint B x
  disjoint B z
  disjoint x z
  disjoint M x
  disjoint M z
  disjoint .o. x
  disjoint .o. z
  assert |- ( A. z e. B E. x e. B ( z .o. x ) =/= x -> M e/ Mnd )

  proof
    vz
    cv
    #
    vx
    cv
    #
    c.op
    co
    #
    @1
    wne
    #
    vx
    cB
    wrex
    #
    vz
    cB
    wral
    #
    cM
    cmnd
    wcel
    #
    wn
    cM
    cmnd
    wnel
    @5
    cM
    csgrp
    wcel
    #
    @2
    @1
    wceq
    #
    @1
    @0
    c.op
    co
    @1
    wceq
    #
    wa
    #
    vx
    cB
    wral
    #
    vz
    cB
    wrex
    #
    wa
    @6
    @5
    @12
    @7
    @5
    @10
    wn
    #
    vx
    cB
    wrex
    #
    vz
    cB
    wral
    #
    @12
    wn
    #
    @4
    @14
    vz
    cB
    @3
    @13
    vx
    cB
    @3
    @8
    @9
    @2
    @1
    neneq
    intnanrd
    reximi
    ralimi
    @15
    @11
    wn
    #
    vz
    cB
    wral
    @16
    @14
    @17
    vz
    cB
    @10
    vx
    cB
    rexnal
    ralbii
    @11
    vz
    cB
    ralnex
    bitri
    sylib
    intnand
    cB
    c.op
    vz
    cM
    vx
    isnmnd.b
    isnmnd.o
    ismnddef
    sylnibr
    cM
    cmnd
    df-nel
    sylibr
end
