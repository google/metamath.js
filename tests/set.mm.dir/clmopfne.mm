include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "c0g.mm"
include "wne.mm"
include "clmlmod.mm"
include "c1.mm"
include "cc0.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqid.mm"
include "clm1.mm"
include "clm0.mm"
include "3netr3d.mm"
include "cbs.mm"
include "lmodfopne.mm"
include "syl2anc.mm"

theorem clmopfne
  let c.pl: class .+
  let c.x: class .x.
  let cW: class W
  assume clmopfne.t: |- .x. = ( .sf ` W )
  assume clmopfne.a: |- .+ = ( +f ` W )


  assert |- ( W e. CMod -> .+ =/= .x. )

  proof
    cW
    cclm
    wcel
    #
    cW
    clmod
    wcel
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    @1
    c0g
    cfv
    #
    wne
    c.pl
    c.x
    wne
    cW
    clmlmod
    @0
    c1
    cc0
    @2
    @3
    c1
    cc0
    wne
    @0
    ax-1ne0
    a1i
    @1
    cW
    @1
    eqid
    #
    clm1
    @1
    cW
    @4
    clm0
    3netr3d
    c.pl
    @1
    c.x
    @2
    @1
    cbs
    cfv
    #
    cW
    cbs
    cfv
    #
    cW
    @3
    clmopfne.t
    clmopfne.a
    @6
    eqid
    @4
    @5
    eqid
    @3
    eqid
    @2
    eqid
    lmodfopne
    syl2anc
end
