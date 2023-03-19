include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "cplusg.mm"
include "cvsca.mm"
include "eqidd.mm"
include "wceq.mm"
include "a1i.mm"
include "clss.mm"
include "wss.mm"
include "ssid.mm"
include "lmodbn0.mm"
include "cv.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "simpl.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "islssd.mm"

theorem lss1
  let cS: class S
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let cU: class U
  assume lssss.v: |- V = ( Base ` W )
  assume lssss.s: |- S = ( LSubSp ` W )


  assert |- ( W e. LMod -> V e. S )

  proof
    cW
    clmod
    wcel
    #
    vx
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cW
    cplusg
    cfv
    #
    cS
    cW
    cvsca
    cfv
    #
    cV
    @1
    cV
    cW
    va
    vb
    @0
    @1
    eqidd
    @0
    @2
    eqidd
    cV
    cW
    cbs
    cfv
    wceq
    @0
    lssss.v
    a1i
    @0
    @3
    eqidd
    @0
    @4
    eqidd
    cS
    cW
    clss
    cfv
    wceq
    @0
    lssss.s
    a1i
    cV
    cV
    wss
    @0
    cV
    ssid
    a1i
    cV
    cW
    lssss.v
    lmodbn0
    @0
    vx
    cv
    #
    @2
    wcel
    #
    va
    cv
    #
    cV
    wcel
    #
    vb
    cv
    #
    cV
    wcel
    #
    w3a
    #
    wa
    @0
    @5
    @7
    @4
    co
    #
    cV
    wcel
    #
    @10
    @12
    @9
    @3
    co
    cV
    wcel
    @0
    @11
    simpl
    @0
    @6
    @8
    @13
    @10
    @5
    @4
    @1
    @2
    cV
    cW
    @7
    lssss.v
    @1
    eqid
    @4
    eqid
    @2
    eqid
    lmodvscl
    3adant3r3
    @0
    @6
    @8
    @10
    simpr3
    @3
    cV
    cW
    @12
    @9
    lssss.v
    @3
    eqid
    lmodvacl
    syl3anc
    islssd
end
