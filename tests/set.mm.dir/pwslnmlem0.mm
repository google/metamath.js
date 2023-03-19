include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cfn.mm"
include "clnm.mm"
include "c0.mm"
include "cvv.mm"
include "0ex.mm"
include "pwslmod.mm"
include "mpan2.mm"
include "cmap.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "pwsbas.mm"
include "csn.mm"
include "c1o.mm"
include "fvex.mm"
include "map0e.mm"
include "ax-mp.mm"
include "df1o2.mm"
include "eqtri.mm"
include "snfi.mm"
include "eqeltri.mm"
include "syl6eqelr.mm"
include "filnm.mm"
include "syl2anc.mm"

theorem pwslnmlem0
  let cW: class W
  let cY: class Y
  assume pwslnmlem0.y: |- Y = ( W ^s (/) )


  assert |- ( W e. LMod -> Y e. LNoeM )

  proof
    cW
    clmod
    wcel
    #
    cY
    clmod
    wcel
    #
    cY
    cbs
    cfv
    #
    cfn
    wcel
    cY
    clnm
    wcel
    @0
    c0
    cvv
    wcel
    #
    @1
    0ex
    cW
    c0
    cvv
    cY
    pwslnmlem0.y
    pwslmod
    mpan2
    @0
    @2
    cW
    cbs
    cfv
    #
    c0
    cmap
    co
    #
    cfn
    @0
    @3
    @5
    @2
    wceq
    0ex
    @4
    cW
    c0
    clmod
    cvv
    cY
    pwslnmlem0.y
    @4
    eqid
    pwsbas
    mpan2
    @5
    c0
    csn
    #
    cfn
    @5
    c1o
    @6
    @4
    cvv
    wcel
    @5
    c1o
    wceq
    cW
    cbs
    fvex
    @4
    cvv
    map0e
    ax-mp
    df1o2
    eqtri
    c0
    snfi
    eqeltri
    syl6eqelr
    @2
    cY
    @2
    eqid
    filnm
    syl2anc
end
