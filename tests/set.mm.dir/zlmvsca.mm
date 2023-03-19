include "cvv.mm"
include "wcel.mm"
include "cvsca.mm"
include "cfv.mm"
include "wceq.mm"
include "cnx.mm"
include "csca.mm"
include "zring.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "zlmval.mm"
include "fveq2d.mm"
include "ovex.mm"
include "cmg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "vscaid.mm"
include "setsid.mm"
include "mp2an.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "czlm.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem zlmvsca
  let c.x: class .x.
  let cG: class G
  let cW: class W
  assume zlmbas.w: |- W = ( ZMod ` G )
  assume zlmvsca.2: |- .x. = ( .g ` G )


  assert |- .x. = ( .s ` W )

  proof
    cG
    cvv
    wcel
    #
    c.x
    cW
    cvsca
    cfv
    #
    wceq
    @0
    @1
    cG
    cnx
    csca
    cfv
    zring
    cop
    #
    csts
    co
    #
    cnx
    cvsca
    cfv
    #
    c.x
    cop
    csts
    co
    #
    cvsca
    cfv
    #
    c.x
    @0
    cW
    @5
    cvsca
    c.x
    cG
    cvv
    cW
    zlmbas.w
    zlmvsca.2
    zlmval
    fveq2d
    @3
    cvv
    wcel
    c.x
    cvv
    wcel
    c.x
    @6
    wceq
    cG
    @2
    csts
    ovex
    c.x
    cG
    cmg
    cfv
    #
    cvv
    zlmvsca.2
    cG
    cmg
    fvex
    eqeltri
    cvv
    c.x
    cvsca
    cvv
    @3
    vscaid
    setsid
    mp2an
    syl6reqr
    @0
    wn
    #
    c0
    c0
    cvsca
    cfv
    c.x
    @1
    cvsca
    @4
    vscaid
    str0
    @8
    c.x
    @7
    c0
    zlmvsca.2
    cG
    cmg
    fvprc
    syl5eq
    @8
    cW
    c0
    cvsca
    @8
    cW
    cG
    czlm
    cfv
    c0
    zlmbas.w
    cG
    czlm
    fvprc
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
end
