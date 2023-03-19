include "wfun.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "c2.mm"
include "cdm.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "wn.mm"
include "fundif.mm"
include "fundmge2nop0.mm"
include "sylan.mm"

theorem fundmge2nop
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Fun G /\ 2 <_ ( # ` dom G ) ) -> -. G e. ( _V X. _V ) )

  proof
    cG
    wfun
    cG
    c0
    csn
    #
    cdif
    wfun
    c2
    cG
    cdm
    chash
    cfv
    cle
    wbr
    cG
    cvv
    cvv
    cxp
    wcel
    wn
    @0
    cG
    fundif
    cG
    fundmge2nop0
    sylan
end
