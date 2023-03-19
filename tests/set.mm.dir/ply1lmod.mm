include "crg.mm"
include "wcel.mm"
include "cps1.mm"
include "cfv.mm"
include "clmod.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "clss.mm"
include "eqid.mm"
include "psr1lmod.mm"
include "cpl1.mm"
include "ply1bas.mm"
include "ply1lss.mm"
include "syl5eqelr.mm"
include "ply1val.mm"
include "lsslmod.mm"
include "syl2anc.mm"

theorem ply1lmod
  let cP: class P
  let cR: class R
  assume ply1lmod.p: |- P = ( Poly1 ` R )


  assert |- ( R e. Ring -> P e. LMod )

  proof
    cR
    crg
    wcel
    #
    cR
    cps1
    cfv
    #
    clmod
    wcel
    c1o
    cR
    cmpl
    co
    cbs
    cfv
    #
    @1
    clss
    cfv
    #
    wcel
    cP
    clmod
    wcel
    @1
    cR
    @1
    eqid
    #
    psr1lmod
    @0
    @2
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    @3
    @5
    cR
    @1
    @6
    @5
    eqid
    #
    @4
    @6
    eqid
    #
    ply1bas
    @5
    cR
    @1
    @6
    @7
    @4
    @8
    ply1lss
    syl5eqelr
    @3
    @2
    @1
    cP
    cP
    cR
    @1
    ply1lmod.p
    @4
    ply1val
    @3
    eqid
    lsslmod
    syl2anc
end
