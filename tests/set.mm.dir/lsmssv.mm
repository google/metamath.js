include "cmnd.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "cmpt2.mm"
include "crn.mm"
include "eqid.mm"
include "lsmvalx.mm"
include "cxp.mm"
include "wf.mm"
include "wral.mm"
include "wa.mm"
include "simpl1.mm"
include "simp2.mm"
include "sselda.mm"
include "adantrr.mm"
include "simp3.mm"
include "adantrl.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "frn.mm"
include "syl.mm"
include "eqsstrd.mm"

theorem lsmssv
  let cB: class B
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cV: class V
  assume lsmless2.v: |- B = ( Base ` G )
  assume lsmless2.s: |- .(+) = ( LSSum ` G )


  assert |- ( ( G e. Mnd /\ T C_ B /\ U C_ B ) -> ( T .(+) U ) C_ B )

  proof
    cG
    cmnd
    wcel
    #
    cT
    cB
    wss
    #
    cU
    cB
    wss
    #
    w3a
    #
    cT
    cU
    c.po
    co
    vx
    vy
    cT
    cU
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    crn
    #
    cB
    vx
    vy
    cB
    @6
    c.po
    cT
    cU
    cG
    cmnd
    lsmless2.v
    @6
    eqid
    #
    lsmless2.s
    lsmvalx
    @3
    cT
    cU
    cxp
    #
    cB
    @8
    wf
    #
    @9
    cB
    wss
    @3
    @7
    cB
    wcel
    #
    vy
    cU
    wral
    vx
    cT
    wral
    @12
    @3
    @13
    vx
    vy
    cT
    cU
    @3
    @4
    cT
    wcel
    #
    @5
    cU
    wcel
    #
    wa
    #
    wa
    @0
    @4
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @13
    @0
    @1
    @2
    @16
    simpl1
    @3
    @14
    @17
    @15
    @3
    cT
    cB
    @4
    @0
    @1
    @2
    simp2
    sselda
    adantrr
    @3
    @15
    @18
    @14
    @3
    cU
    cB
    @5
    @0
    @1
    @2
    simp3
    sselda
    adantrl
    cB
    @6
    cG
    @4
    @5
    lsmless2.v
    @10
    mndcl
    syl3anc
    ralrimivva
    vx
    vy
    cT
    cU
    @7
    cB
    @8
    @8
    eqid
    fmpt2
    sylib
    @11
    cB
    @8
    frn
    syl
    eqsstrd
end
