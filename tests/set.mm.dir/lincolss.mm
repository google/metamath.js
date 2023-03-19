include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wa.mm"
include "csca.mm"
include "cplusg.mm"
include "clss.mm"
include "cvsca.mm"
include "clinco.mm"
include "co.mm"
include "eqidd.mm"
include "cv.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "eqid.mm"
include "lcoval.mm"
include "simpl.mm"
include "syl6bi.mm"
include "ssrdv.mm"
include "c0.mm"
include "wne.mm"
include "lcoel0.mm"
include "ne0i.mm"
include "syl.mm"
include "lincsumscmcl.mm"
include "islssd.mm"

theorem lincolss
  let cM: class M
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vv: setvar v
  let vx: setvar x
  let vk: setvar k


  assert |- ( ( M e. LMod /\ V e. ~P ( Base ` M ) ) -> ( M LinCo V ) e. ( LSubSp ` M ) )

  proof
    cM
    clmod
    wcel
    cV
    cM
    cbs
    cfv
    #
    cpw
    wcel
    wa
    #
    vx
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    cM
    cplusg
    cfv
    #
    cM
    clss
    cfv
    #
    cM
    cvsca
    cfv
    #
    cM
    cV
    clinco
    co
    #
    @2
    @0
    cM
    va
    vb
    @1
    @2
    eqidd
    @1
    @3
    eqidd
    @1
    @0
    eqidd
    @1
    @4
    eqidd
    @1
    @6
    eqidd
    @1
    @5
    eqidd
    @1
    vv
    @7
    @0
    @1
    vv
    cv
    #
    @7
    wcel
    @8
    @0
    wcel
    #
    vs
    cv
    #
    @2
    c0g
    cfv
    cfsupp
    wbr
    @8
    @10
    cV
    cM
    clinc
    cfv
    co
    wceq
    wa
    vs
    @3
    cV
    cmap
    co
    wrex
    #
    wa
    @9
    @0
    @8
    @3
    @2
    cM
    cV
    clmod
    vs
    @0
    eqid
    @2
    eqid
    @3
    eqid
    #
    lcoval
    @9
    @11
    simpl
    syl6bi
    ssrdv
    @1
    cM
    c0g
    cfv
    #
    @7
    wcel
    @7
    c0
    wne
    cM
    cV
    lcoel0
    @7
    @13
    ne0i
    syl
    vb
    cv
    vx
    cv
    va
    cv
    @4
    @3
    @6
    cM
    cV
    @6
    eqid
    @12
    @4
    eqid
    lincsumscmcl
    islssd
end
