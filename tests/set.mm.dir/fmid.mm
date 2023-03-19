include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cfm.mm"
include "co.mm"
include "cv.mm"
include "cima.mm"
include "wceq.mm"
include "cfg.mm"
include "wrex.mm"
include "cfbas.mm"
include "wfo.mm"
include "wb.mm"
include "filfbas.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1ofo.mm"
include "ax-mp.mm"
include "eqid.mm"
include "elfm3.mm"
include "sylancl.mm"
include "fgfil.mm"
include "rexeqdv.mm"
include "wa.mm"
include "wss.mm"
include "filelss.mm"
include "resiima.mm"
include "syl.mm"
include "eqeq2d.mm"
include "equcom.mm"
include "syl6bbr.mm"
include "rexbidva.mm"
include "risset.mm"
include "3bitrd.mm"
include "eqrdv.mm"

theorem fmid
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let cB: class B
  let cG: class G
  let cV: class V
  let vx: setvar x
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cY: class Y
  let cZ: class Z


  assert |- ( F e. ( Fil ` X ) -> ( ( X FilMap ( _I |` X ) ) ` F ) = F )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    #
    vt
    cF
    cX
    cid
    cX
    cres
    #
    cfm
    co
    cfv
    #
    cF
    @0
    vt
    cv
    #
    @2
    wcel
    #
    @3
    @1
    vs
    cv
    #
    cima
    #
    wceq
    #
    vs
    cX
    cF
    cfg
    co
    #
    wrex
    #
    @7
    vs
    cF
    wrex
    #
    @3
    cF
    wcel
    #
    @0
    cF
    cX
    cfbas
    cfv
    wcel
    cX
    cX
    @1
    wfo
    #
    @4
    @9
    wb
    cF
    cX
    filfbas
    cX
    cX
    @1
    wf1o
    @12
    cX
    f1oi
    cX
    cX
    @1
    f1ofo
    ax-mp
    vs
    @3
    cF
    @1
    @8
    cX
    cX
    @8
    eqid
    elfm3
    sylancl
    @0
    @7
    vs
    @8
    cF
    cF
    cX
    fgfil
    rexeqdv
    @0
    @10
    @5
    @3
    wceq
    #
    vs
    cF
    wrex
    @11
    @0
    @7
    @13
    vs
    cF
    @0
    @5
    cF
    wcel
    wa
    #
    @7
    @3
    @5
    wceq
    @13
    @14
    @6
    @5
    @3
    @14
    @5
    cX
    wss
    @6
    @5
    wceq
    @5
    cF
    cX
    filelss
    cX
    @5
    resiima
    syl
    eqeq2d
    vs
    vt
    equcom
    syl6bbr
    rexbidva
    vs
    @3
    cF
    risset
    syl6bbr
    3bitrd
    eqrdv
end
