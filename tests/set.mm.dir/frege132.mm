include "ccnv.mm"
include "wfun.mm"
include "ctcl.mm"
include "cfv.mm"
include "csn.mm"
include "cima.mm"
include "cid.mm"
include "cun.mm"
include "whe.mm"
include "wi.mm"
include "wbr.mm"
include "wn.mm"
include "frege131.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege132
  let cR: class R
  let cU: class U
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  assume frege130.m: |- M e. U
  assume frege130.r: |- R e. V


  assert |- ( ( R hereditary ( ( `' ( t+ ` R ) " { M } ) u. ( ( ( t+ ` R ) u. _I ) " { M } ) ) -> ( X ( t+ ` R ) M -> ( X ( t+ ` R ) Y -> ( -. Y ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) Y ) ) ) ) -> ( Fun `' `' R -> ( X ( t+ ` R ) M -> ( X ( t+ ` R ) Y -> ( -. Y ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) Y ) ) ) ) )

  proof
    cR
    ccnv
    ccnv
    wfun
    #
    cR
    ctcl
    cfv
    #
    ccnv
    cM
    csn
    #
    cima
    @1
    cid
    cun
    #
    @2
    cima
    cun
    cR
    whe
    #
    wi
    @4
    cX
    cM
    @1
    wbr
    cX
    cY
    @1
    wbr
    cY
    cM
    @1
    wbr
    wn
    cM
    cY
    @3
    wbr
    wi
    wi
    wi
    #
    wi
    @0
    @5
    wi
    wi
    cR
    cU
    cM
    cV
    frege130.m
    frege130.r
    frege131
    @0
    @4
    @5
    frege9
    ax-mp
end
