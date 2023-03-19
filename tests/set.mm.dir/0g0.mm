include "c0.mm"
include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cio.mm"
include "base0.mm"
include "eqid.mm"
include "grpidval.mm"
include "weu.mm"
include "wn.mm"
include "wex.mm"
include "noel.mm"
include "intnanr.mm"
include "nex.mm"
include "euex.mm"
include "mto.mm"
include "iotanul.mm"
include "ax-mp.mm"
include "eqtr2i.mm"

theorem 0g0
  let ve: setvar e
  let vg: setvar g
  let vx: setvar x


  assert |- (/) = ( 0g ` (/) )

  proof
    c0
    c0g
    cfv
    #
    ve
    cv
    #
    c0
    wcel
    #
    @1
    vx
    cv
    #
    c0
    cplusg
    cfv
    #
    co
    @3
    wceq
    @3
    @1
    @4
    co
    @3
    wceq
    wa
    vx
    c0
    wral
    #
    wa
    #
    ve
    cio
    #
    c0
    vx
    c0
    @4
    ve
    c0
    @0
    base0
    @4
    eqid
    @0
    eqid
    grpidval
    @6
    ve
    weu
    #
    wn
    @7
    c0
    wceq
    @8
    @6
    ve
    wex
    @6
    ve
    @2
    @5
    @1
    noel
    intnanr
    nex
    @6
    ve
    euex
    mto
    @6
    ve
    iotanul
    ax-mp
    eqtr2i
end
