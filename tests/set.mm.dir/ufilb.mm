include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "wn.mm"
include "cdif.mm"
include "ufilss.mm"
include "ord.mm"
include "wi.mm"
include "cfil.mm"
include "cfbas.mm"
include "ufilfil.mm"
include "filfbas.mm"
include "fbncp.mm"
include "ex.mm"
include "con2d.mm"
include "3syl.mm"
include "adantr.mm"
include "impbid.mm"

theorem ufilb
  let cS: class S
  let cF: class F
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cG: class G


  assert |- ( ( F e. ( UFil ` X ) /\ S C_ X ) -> ( -. S e. F <-> ( X \ S ) e. F ) )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cS
    cF
    wcel
    #
    wn
    #
    cX
    cS
    cdif
    cF
    wcel
    #
    @2
    @3
    @5
    cS
    cF
    cX
    ufilss
    ord
    @0
    @5
    @4
    wi
    #
    @1
    @0
    cF
    cX
    cfil
    cfv
    wcel
    cF
    cX
    cfbas
    cfv
    wcel
    #
    @6
    cF
    cX
    ufilfil
    cF
    cX
    filfbas
    @7
    @3
    @5
    @7
    @3
    @5
    wn
    cS
    cX
    cF
    cX
    fbncp
    ex
    con2d
    3syl
    adantr
    impbid
end
