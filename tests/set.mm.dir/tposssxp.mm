include "ctpos.mm"
include "cdm.mm"
include "ccnv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "cuni.mm"
include "cmpt.mm"
include "crn.mm"
include "cxp.mm"
include "ccom.mm"
include "df-tpos.mm"
include "cossxp.mm"
include "eqsstri.mm"
include "wss.mm"
include "eqid.mm"
include "dmmptss.mm"
include "xpss1.mm"
include "ax-mp.mm"
include "sstri.mm"

theorem tposssxp
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- tpos F C_ ( ( `' dom F u. { (/) } ) X. ran F )

  proof
    cF
    ctpos
    #
    vx
    cF
    cdm
    ccnv
    c0
    csn
    cun
    #
    vx
    cv
    csn
    ccnv
    cuni
    #
    cmpt
    #
    cdm
    #
    cF
    crn
    #
    cxp
    #
    @1
    @5
    cxp
    #
    @0
    cF
    @3
    ccom
    @6
    vx
    cF
    df-tpos
    cF
    @3
    cossxp
    eqsstri
    @4
    @1
    wss
    @6
    @7
    wss
    vx
    @1
    @2
    @3
    @3
    eqid
    dmmptss
    @4
    @1
    @5
    xpss1
    ax-mp
    sstri
end
