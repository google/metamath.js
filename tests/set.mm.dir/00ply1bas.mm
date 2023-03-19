include "c0.mm"
include "cpl1.mm"
include "cfv.mm"
include "cbs.mm"
include "cv.mm"
include "wcel.mm"
include "noel.mm"
include "c1o.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "eqid.mm"
include "base0.mm"
include "ply1basf.mm"
include "0nn0.mm"
include "fconst6.mm"
include "nn0ex.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "elmap.mm"
include "mpbir.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "mto.mm"
include "2false.mm"
include "eqriv.mm"

theorem 00ply1bas
  let va: setvar a


  assert |- (/) = ( Base ` ( Poly1 ` (/) ) )

  proof
    va
    c0
    c0
    cpl1
    cfv
    #
    cbs
    cfv
    #
    va
    cv
    #
    c0
    wcel
    @2
    @1
    wcel
    #
    @2
    noel
    @3
    c1o
    cc0
    csn
    cxp
    #
    @2
    cfv
    #
    c0
    wcel
    #
    @5
    noel
    @3
    cn0
    c1o
    cmap
    co
    #
    c0
    @2
    wf
    @4
    @7
    wcel
    #
    @6
    @1
    @0
    c0
    @2
    c0
    @0
    eqid
    @1
    eqid
    base0
    ply1basf
    @8
    c1o
    cn0
    @4
    wf
    c1o
    cc0
    cn0
    0nn0
    fconst6
    cn0
    c1o
    @4
    nn0ex
    c1o
    con0
    1on
    elexi
    elmap
    mpbir
    @7
    c0
    @4
    @2
    ffvelrn
    sylancl
    mto
    2false
    eqriv
end
