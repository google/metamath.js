include "cmnd.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cfv.mm"
include "cword.mm"
include "cgsu.mm"
include "co.mm"
include "submid.mm"
include "gsumwsubmcl.mm"
include "sylan.mm"

theorem gsumwcl
  let cB: class B
  let cG: class G
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let cX: class X
  assume gsumwcl.b: |- B = ( Base ` G )


  assert |- ( ( G e. Mnd /\ W e. Word B ) -> ( G gsum W ) e. B )

  proof
    cG
    cmnd
    wcel
    cB
    cG
    csubmnd
    cfv
    wcel
    cW
    cB
    cword
    wcel
    cG
    cW
    cgsu
    co
    cB
    wcel
    cB
    cG
    gsumwcl.b
    submid
    cB
    cG
    cW
    gsumwsubmcl
    sylan
end
