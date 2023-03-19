include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "crg.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashgt12el.mm"
include "mpan.mm"
include "adantl.mm"
include "wi.mm"
include "w3a.mm"
include "ring1eq0.mm"
include "necon3d.mm"
include "3expib.mm"
include "adantr.mm"
include "com3l.mm"
include "rexlimivv.mm"
include "mpcom.mm"

theorem ring1ne0
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume ring1ne0.b: |- B = ( Base ` R )
  assume ring1ne0.u: |- .1. = ( 1r ` R )
  assume ring1ne0.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ 1 < ( # ` B ) ) -> .1. =/= .0. )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    vy
    cB
    wrex
    vx
    cB
    wrex
    #
    cR
    crg
    wcel
    #
    c1
    cB
    chash
    cfv
    clt
    wbr
    #
    wa
    #
    c.1
    c.0
    wne
    #
    @5
    @3
    @4
    cB
    cvv
    wcel
    @5
    @3
    cB
    cR
    cbs
    cfv
    cvv
    ring1ne0.b
    cR
    cbs
    fvex
    eqeltri
    cB
    cvv
    vx
    vy
    hashgt12el
    mpan
    adantl
    @2
    @6
    @7
    wi
    vx
    vy
    cB
    cB
    @6
    @0
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    wa
    #
    @2
    @7
    @4
    @10
    @2
    @7
    wi
    #
    wi
    @5
    @4
    @8
    @9
    @11
    @4
    @8
    @9
    w3a
    c.1
    c.0
    @0
    @1
    cB
    cR
    c.1
    @0
    @1
    c.0
    ring1ne0.b
    ring1ne0.u
    ring1ne0.z
    ring1eq0
    necon3d
    3expib
    adantr
    com3l
    rexlimivv
    mpcom
end
