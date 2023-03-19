include "wcel.mm"
include "wrel.mm"
include "cdm.mm"
include "ctpos.mm"
include "wceq.mm"
include "cxp.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "eqid.mm"
include "matbas2i.mm"
include "elmapi.mm"
include "syl.mm"
include "frel.mm"
include "relxp.mm"
include "fdm.mm"
include "releqd.mm"
include "mpbiri.mm"
include "tpostpos2.mm"
include "syl2anc.mm"

theorem mattpostpos
  let cA: class A
  let cB: class B
  let cR: class R
  let cM: class M
  let cN: class N
  assume mattposcl.a: |- A = ( N Mat R )
  assume mattposcl.b: |- B = ( Base ` A )


  assert |- ( M e. B -> tpos tpos M = M )

  proof
    cM
    cB
    wcel
    #
    cM
    wrel
    #
    cM
    cdm
    #
    wrel
    #
    cM
    ctpos
    ctpos
    cM
    wceq
    @0
    cN
    cN
    cxp
    #
    cR
    cbs
    cfv
    #
    cM
    wf
    #
    @1
    @0
    cM
    @5
    @4
    cmap
    co
    wcel
    @6
    cA
    cB
    cR
    @5
    cM
    cN
    mattposcl.a
    @5
    eqid
    mattposcl.b
    matbas2i
    cM
    @5
    @4
    elmapi
    syl
    #
    @4
    @5
    cM
    frel
    syl
    @0
    @3
    @4
    wrel
    cN
    cN
    relxp
    @0
    @2
    @4
    @0
    @6
    @2
    @4
    wceq
    @7
    @4
    @5
    cM
    fdm
    syl
    releqd
    mpbiri
    cM
    tpostpos2
    syl2anc
end
