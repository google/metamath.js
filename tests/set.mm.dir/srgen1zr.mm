include "csrg.mm"
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
include "srg0cl.mm"
include "3ad2ant1.mm"
include "en1eqsnbi.mm"
include "adantl.mm"
include "srg1zr.mm"
include "bitrd.mm"
include "mpdan.mm"

theorem srgen1zr
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.as: class .*
  let cZ: class Z
  assume srg1zr.b: |- B = ( Base ` R )
  assume srg1zr.p: |- .+ = ( +g ` R )
  assume srg1zr.t: |- .* = ( .r ` R )
  assume srgen1zr.p: |- Z = ( 0g ` R )


  assert |- ( ( R e. SRing /\ .+ Fn ( B X. B ) /\ .* Fn ( B X. B ) ) -> ( B ~~ 1o <-> ( .+ = { <. <. Z , Z >. , Z >. } /\ .* = { <. <. Z , Z >. , Z >. } ) ) )

  proof
    cR
    csrg
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
    #
    cZ
    cB
    wcel
    #
    cB
    c1o
    cen
    wbr
    #
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
    @7
    wceq
    wa
    #
    wb
    @0
    @2
    @5
    @3
    cB
    cR
    cZ
    srg1zr.b
    srgen1zr.p
    srg0cl
    3ad2ant1
    @4
    @5
    wa
    @6
    cB
    cZ
    csn
    wceq
    #
    @8
    @5
    @6
    @9
    wb
    @4
    cZ
    cB
    en1eqsnbi
    adantl
    cB
    c.pl
    cR
    c.as
    cZ
    srg1zr.b
    srg1zr.p
    srg1zr.t
    srg1zr
    bitrd
    mpdan
end
