include "clmod.mm"
include "wcel.mm"
include "cvsca.mm"
include "cfv.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "id.mm"
include "eqidd.mm"
include "cabl.mm"
include "cghm.mm"
include "co.mm"
include "lmodabl.mm"
include "invghm.mm"
include "sylib.mm"
include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "lmodvsinv2.mm"
include "eqcomd.mm"
include "3expb.mm"
include "islmhmd.mm"

theorem invlmhm
  let cI: class I
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume invlmhm.b: |- I = ( invg ` M )


  assert |- ( M e. LMod -> I e. ( M LMHom M ) )

  proof
    cM
    clmod
    wcel
    #
    vx
    vy
    cM
    cM
    cM
    cvsca
    cfv
    #
    @1
    cI
    cM
    csca
    cfv
    #
    @2
    @2
    cbs
    cfv
    #
    cM
    cbs
    cfv
    #
    @4
    eqid
    #
    @1
    eqid
    #
    @6
    @2
    eqid
    #
    @7
    @3
    eqid
    #
    @0
    id
    #
    @9
    @0
    @2
    eqidd
    @0
    cM
    cabl
    wcel
    cI
    cM
    cM
    cghm
    co
    wcel
    cM
    lmodabl
    @4
    cM
    cI
    @5
    invlmhm.b
    invghm
    sylib
    @0
    vx
    cv
    #
    @3
    wcel
    #
    vy
    cv
    #
    @4
    wcel
    #
    @10
    @12
    @1
    co
    cI
    cfv
    #
    @10
    @12
    cI
    cfv
    @1
    co
    #
    wceq
    @0
    @11
    @13
    w3a
    @15
    @14
    @4
    @10
    @1
    @2
    @3
    cI
    cM
    @12
    @5
    @7
    @6
    invlmhm.b
    @8
    lmodvsinv2
    eqcomd
    3expb
    islmhmd
end
