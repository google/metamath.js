include "cuhgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "wa.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "uhgredgn0.mm"
include "eldifad.mm"

theorem edguhgr
  let cE: class E
  let cG: class G


  assert |- ( ( G e. UHGraph /\ E e. ( Edg ` G ) ) -> E e. ~P ( Vtx ` G ) )

  proof
    cG
    cuhgr
    wcel
    cE
    cG
    cedg
    cfv
    wcel
    wa
    cE
    cG
    cvtx
    cfv
    cpw
    c0
    csn
    cE
    cG
    uhgredgn0
    eldifad
end
