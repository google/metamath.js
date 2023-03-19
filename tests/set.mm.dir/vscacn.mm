include "ctlm.mm"
include "wcel.mm"
include "ctmd.mm"
include "clmod.mm"
include "ctrg.mm"
include "w3a.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "istlm.mm"
include "simprbi.mm"

theorem vscacn
  let c.x: class .x.
  let cF: class F
  let cJ: class J
  let cK: class K
  let cW: class W
  let vw: setvar w
  assume istlm.s: |- .x. = ( .sf ` W )
  assume istlm.j: |- J = ( TopOpen ` W )
  assume istlm.f: |- F = ( Scalar ` W )
  assume istlm.k: |- K = ( TopOpen ` F )


  assert |- ( W e. TopMod -> .x. e. ( ( K tX J ) Cn J ) )

  proof
    cW
    ctlm
    wcel
    cW
    ctmd
    wcel
    cW
    clmod
    wcel
    cF
    ctrg
    wcel
    w3a
    c.x
    cK
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    c.x
    cF
    cJ
    cK
    cW
    istlm.s
    istlm.j
    istlm.f
    istlm.k
    istlm
    simprbi
end
