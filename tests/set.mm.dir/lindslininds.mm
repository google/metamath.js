include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "csca.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wi.mm"
include "cmap.mm"
include "wss.mm"
include "cvsca.mm"
include "csn.mm"
include "cdif.mm"
include "clspn.mm"
include "wn.mm"
include "clininds.mm"
include "clinds.mm"
include "eqid.mm"
include "lindslinindsimp1.mm"
include "lindslinindsimp2.mm"
include "impbid.mm"
include "islininds.mm"
include "wb.mm"
include "islinds2.mm"
include "adantl.mm"
include "3bitr4d.mm"

theorem lindslininds
  let cS: class S
  let cM: class M
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( S e. V /\ M e. LMod ) -> ( S linIndS M <-> S e. ( LIndS ` M ) ) )

  proof
    cS
    cV
    wcel
    #
    cM
    clmod
    wcel
    #
    wa
    #
    cS
    cM
    cbs
    cfv
    #
    cpw
    wcel
    vf
    cv
    #
    cM
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    @4
    cS
    cM
    clinc
    cfv
    co
    cM
    c0g
    cfv
    #
    wceq
    wa
    vx
    cv
    @4
    cfv
    @6
    wceq
    vx
    cS
    wral
    wi
    vf
    @5
    cbs
    cfv
    #
    cS
    cmap
    co
    wral
    wa
    #
    cS
    @3
    wss
    vg
    cv
    vs
    cv
    #
    cM
    cvsca
    cfv
    #
    co
    cS
    @10
    csn
    cdif
    cM
    clspn
    cfv
    #
    cfv
    wcel
    wn
    vg
    @8
    @6
    csn
    cdif
    wral
    vs
    cS
    wral
    wa
    #
    cS
    cM
    clininds
    wbr
    cS
    cM
    clinds
    cfv
    wcel
    #
    @2
    @9
    @13
    vx
    vg
    @8
    @5
    cS
    vf
    cM
    cV
    @6
    @7
    vs
    @5
    eqid
    #
    @8
    eqid
    #
    @6
    eqid
    #
    @7
    eqid
    #
    lindslinindsimp1
    vx
    vg
    @8
    @5
    cS
    vf
    cM
    cV
    @6
    @7
    vs
    @15
    @16
    @17
    @18
    lindslinindsimp2
    impbid
    vx
    @3
    @5
    cS
    vf
    @8
    cM
    cV
    clmod
    @6
    @7
    @3
    eqid
    #
    @18
    @15
    @16
    @17
    islininds
    @1
    @14
    @13
    wb
    @0
    vs
    @3
    @5
    @11
    vg
    cS
    @12
    @8
    cM
    clmod
    @6
    @19
    @11
    eqid
    @12
    eqid
    @15
    @16
    @17
    islinds2
    adantl
    3bitr4d
end
