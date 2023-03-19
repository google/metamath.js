include "crg.mm"
include "wcel.mm"
include "cxp.mm"
include "wfn.mm"
include "w3a.mm"
include "wa.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "csn.mm"
include "wceq.mm"
include "cop.mm"
include "wb.mm"
include "en1eqsnbi.mm"
include "adantl.mm"
include "ring1zr.mm"
include "bitrd.mm"

theorem rngen1zr
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.as: class .*
  let cZ: class Z
  assume ring1zr.b: |- B = ( Base ` R )
  assume ring1zr.p: |- .+ = ( +g ` R )
  assume ring1zr.t: |- .* = ( .r ` R )


  assert |- ( ( ( R e. Ring /\ .+ Fn ( B X. B ) /\ .* Fn ( B X. B ) ) /\ Z e. B ) -> ( B ~~ 1o <-> ( .+ = { <. <. Z , Z >. , Z >. } /\ .* = { <. <. Z , Z >. , Z >. } ) ) )

  proof
    cR
    crg
    wcel
    c.pl
    cB
    cB
    cxp
    #
    wfn
    c.as
    @0
    wfn
    w3a
    #
    cZ
    cB
    wcel
    #
    wa
    cB
    c1o
    cen
    wbr
    #
    cB
    cZ
    csn
    wceq
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
    @5
    wceq
    wa
    @2
    @3
    @4
    wb
    @1
    cZ
    cB
    en1eqsnbi
    adantl
    cB
    c.pl
    cR
    c.as
    cZ
    ring1zr.b
    ring1zr.p
    ring1zr.t
    ring1zr
    bitrd
end
