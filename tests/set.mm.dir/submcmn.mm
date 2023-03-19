include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "ccmn.mm"
include "cmnd.mm"
include "submmnd.mm"
include "subcmn.mm"
include "sylan2.mm"

theorem submcmn
  let cS: class S
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume subgabl.h: |- H = ( G |`s S )


  assert |- ( ( G e. CMnd /\ S e. ( SubMnd ` G ) ) -> H e. CMnd )

  proof
    cS
    cG
    csubmnd
    cfv
    wcel
    cG
    ccmn
    wcel
    cH
    cmnd
    wcel
    cH
    ccmn
    wcel
    cS
    cH
    cG
    subgabl.h
    submmnd
    cS
    cG
    cH
    subgabl.h
    subcmn
    sylan2
end
