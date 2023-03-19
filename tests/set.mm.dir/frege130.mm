include "ccnv.mm"
include "wfun.mm"
include "cv.mm"
include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "cid.mm"
include "cun.mm"
include "wi.mm"
include "wal.mm"
include "csn.mm"
include "cima.mm"
include "whe.mm"
include "cvv.mm"
include "vex.mm"
include "frege129.mm"
include "alrimdv.mm"
include "alrimiv.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege130
  let cR: class R
  let cU: class U
  let cM: class M
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume frege130.m: |- M e. U
  assume frege130.r: |- R e. V

  disjoint M a
  disjoint a b
  disjoint R a
  disjoint R b
  assert |- ( ( A. b ( ( -. b ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) b ) -> A. a ( b R a -> ( -. a ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) a ) ) ) -> R hereditary ( ( `' ( t+ ` R ) " { M } ) u. ( ( ( t+ ` R ) u. _I ) " { M } ) ) ) -> ( Fun `' `' R -> R hereditary ( ( `' ( t+ ` R ) " { M } ) u. ( ( ( t+ ` R ) u. _I ) " { M } ) ) ) )

  proof
    cR
    ccnv
    ccnv
    wfun
    #
    vb
    cv
    #
    cM
    cR
    ctcl
    cfv
    #
    wbr
    wn
    cM
    @1
    @2
    cid
    cun
    #
    wbr
    wi
    #
    @1
    va
    cv
    #
    cR
    wbr
    @5
    cM
    @2
    wbr
    wn
    cM
    @5
    @3
    wbr
    wi
    wi
    #
    va
    wal
    wi
    #
    vb
    wal
    #
    wi
    @8
    @2
    ccnv
    cM
    csn
    #
    cima
    @3
    @9
    cima
    cun
    cR
    whe
    #
    wi
    @0
    @10
    wi
    wi
    @0
    @7
    vb
    @0
    @4
    @6
    va
    cR
    cV
    cvv
    cM
    cvv
    cU
    @5
    @1
    va
    vex
    vb
    vex
    frege130.m
    frege130.r
    frege129
    alrimdv
    alrimiv
    @0
    @8
    @10
    frege9
    ax-mp
end
