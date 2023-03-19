include "crg.mm"
include "wcel.mm"
include "csrg.mm"
include "cxp.mm"
include "wfn.mm"
include "csn.mm"
include "wceq.mm"
include "cop.mm"
include "wa.mm"
include "wb.mm"
include "ringsrg.mm"
include "srg1zr.mm"
include "syl3anl1.mm"

theorem ring1zr
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.as: class .*
  let cZ: class Z
  assume ring1zr.b: |- B = ( Base ` R )
  assume ring1zr.p: |- .+ = ( +g ` R )
  assume ring1zr.t: |- .* = ( .r ` R )


  assert |- ( ( ( R e. Ring /\ .+ Fn ( B X. B ) /\ .* Fn ( B X. B ) ) /\ Z e. B ) -> ( B = { Z } <-> ( .+ = { <. <. Z , Z >. , Z >. } /\ .* = { <. <. Z , Z >. , Z >. } ) ) )

  proof
    cR
    crg
    wcel
    cR
    csrg
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
    cZ
    cB
    wcel
    cB
    cZ
    csn
    wceq
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
    @1
    wceq
    wa
    wb
    cR
    ringsrg
    cB
    c.pl
    cR
    c.as
    cZ
    ring1zr.b
    ring1zr.p
    ring1zr.t
    srg1zr
    syl3anl1
end
