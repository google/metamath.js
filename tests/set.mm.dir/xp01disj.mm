include "c0.mm"
include "c1o.mm"
include "wne.mm"
include "csn.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "1n0.mm"
include "necomi.mm"
include "xpsndisj.mm"
include "ax-mp.mm"

theorem xp01disj
  let cA: class A
  let cC: class C


  assert |- ( ( A X. { (/) } ) i^i ( C X. { 1o } ) ) = (/)

  proof
    c0
    c1o
    wne
    cA
    c0
    csn
    cxp
    cC
    c1o
    csn
    cxp
    cin
    c0
    wceq
    c1o
    c0
    1n0
    necomi
    cA
    c0
    cC
    c1o
    xpsndisj
    ax-mp
end
