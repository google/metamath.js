include "crg.mm"
include "wcel.mm"
include "cxp.mm"
include "wfn.mm"
include "w3a.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "ring0cl.mm"
include "3ad2ant1.mm"
include "rngen1zr.mm"
include "mpdan.mm"

theorem ringen1zr
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.as: class .*
  let cZ: class Z
  assume ring1zr.b: |- B = ( Base ` R )
  assume ring1zr.p: |- .+ = ( +g ` R )
  assume ring1zr.t: |- .* = ( .r ` R )
  assume ringen1zr.0: |- Z = ( 0g ` R )


  assert |- ( ( R e. Ring /\ .+ Fn ( B X. B ) /\ .* Fn ( B X. B ) ) -> ( B ~~ 1o <-> ( .+ = { <. <. Z , Z >. , Z >. } /\ .* = { <. <. Z , Z >. , Z >. } ) ) )

  proof
    cR
    crg
    wcel
    #
    c.pl
    cB
    cB
    cxp
    #
    wfn
    #
    c.as
    @1
    wfn
    #
    w3a
    cZ
    cB
    wcel
    #
    cB
    c1o
    cen
    wbr
    c.pl
    cZ
    cZ
    cop
    cZ
    cop
    csn
    #
    wceq
    c.as
    @5
    wceq
    wa
    wb
    @0
    @2
    @4
    @3
    cB
    cR
    cZ
    ring1zr.b
    ringen1zr.0
    ring0cl
    3ad2ant1
    cB
    c.pl
    cR
    c.as
    cZ
    ring1zr.b
    ring1zr.p
    ring1zr.t
    rngen1zr
    mpdan
end
