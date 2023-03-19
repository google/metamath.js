include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "cmeas.mm"
include "cfv.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wdisj.mm"
include "wa.mm"
include "cuni.mm"
include "cesum.mm"
include "wceq.mm"
include "domprobmeas.mm"
include "measvun.mm"
include "syl3an1.mm"

theorem probcun
  let vx: setvar x
  let cA: class A
  let cP: class P

  disjoint A x
  disjoint P x
  assert |- ( ( P e. Prob /\ A e. ~P dom P /\ ( A ~<_ _om /\ Disj_ x e. A x ) ) -> ( P ` U. A ) = sum* x e. A ( P ` x ) )

  proof
    cP
    cprb
    wcel
    cP
    cP
    cdm
    #
    cmeas
    cfv
    wcel
    cA
    @0
    cpw
    wcel
    cA
    com
    cdom
    wbr
    vx
    cA
    vx
    cv
    #
    wdisj
    wa
    cA
    cuni
    cP
    cfv
    cA
    @1
    cP
    cfv
    vx
    cesum
    wceq
    cP
    domprobmeas
    vx
    cA
    @0
    cP
    measvun
    syl3an1
end
