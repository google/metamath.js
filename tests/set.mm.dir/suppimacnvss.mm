include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wne.mm"
include "wex.mm"
include "cab.mm"
include "wb.mm"
include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "csupp.mm"
include "co.mm"
include "wi.mm"
include "exsimpl.mm"
include "pm5.1.mm"
include "eximi.mm"
include "jca.mm"
include "a1i.mm"
include "ss2abdv.mm"
include "wceq.mm"
include "cnvimadfsn.mm"
include "suppvalbr.mm"
include "3sstr4d.mm"

theorem suppimacnvss
  let cR: class R
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( R e. V /\ Z e. W ) -> ( `' R " ( _V \ { Z } ) ) C_ ( R supp Z ) )

  proof
    cR
    cV
    wcel
    cZ
    cW
    wcel
    wa
    #
    vx
    cv
    vy
    cv
    #
    cR
    wbr
    #
    @1
    cZ
    wne
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    @2
    vy
    wex
    #
    @2
    @3
    wb
    #
    vy
    wex
    #
    wa
    #
    vx
    cab
    cR
    ccnv
    cvv
    cZ
    csn
    cdif
    cima
    #
    cR
    cZ
    csupp
    co
    @0
    @5
    @10
    vx
    @5
    @10
    wi
    @0
    @5
    @7
    @9
    @2
    @3
    vy
    exsimpl
    @4
    @8
    vy
    @2
    @3
    pm5.1
    eximi
    jca
    a1i
    ss2abdv
    @11
    @6
    wceq
    @0
    vx
    vy
    cR
    cZ
    cnvimadfsn
    a1i
    vx
    vy
    cR
    cV
    cW
    cZ
    suppvalbr
    3sstr4d
end
