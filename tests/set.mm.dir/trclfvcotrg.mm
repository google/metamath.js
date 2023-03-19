include "cvv.mm"
include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "ccom.mm"
include "wss.mm"
include "trclfvcotr.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "fvprc.mm"
include "0trrel.mm"
include "a1i.mm"
include "id.mm"
include "coeq12d.mm"
include "3sstr4d.mm"
include "syl.mm"
include "pm2.61i.mm"

theorem trclfvcotrg
  let cR: class R


  assert |- ( ( t+ ` R ) o. ( t+ ` R ) ) C_ ( t+ ` R )

  proof
    cR
    cvv
    wcel
    #
    cR
    ctcl
    cfv
    #
    @1
    ccom
    #
    @1
    wss
    #
    cR
    cvv
    trclfvcotr
    @0
    wn
    @1
    c0
    wceq
    #
    @3
    cR
    ctcl
    fvprc
    @4
    c0
    c0
    ccom
    #
    c0
    @2
    @1
    @5
    c0
    wss
    @4
    0trrel
    a1i
    @4
    @1
    c0
    @1
    c0
    @4
    id
    #
    @6
    coeq12d
    @6
    3sstr4d
    syl
    pm2.61i
end
