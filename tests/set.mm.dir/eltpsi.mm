include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ctps.mm"
include "ctop.mm"
include "toptopon.mm"
include "mpbi.mm"
include "eltpsg.mm"
include "ax-mp.mm"

theorem eltpsi
  let cA: class A
  let cJ: class J
  let cK: class K
  assume eltpsi.k: |- K = { <. ( Base ` ndx ) , A >. , <. ( TopSet ` ndx ) , J >. }
  assume eltpsi.u: |- A = U. J
  assume eltpsi.j: |- J e. Top


  assert |- K e. TopSp

  proof
    cJ
    cA
    ctopon
    cfv
    wcel
    #
    cK
    ctps
    wcel
    cJ
    ctop
    wcel
    @0
    eltpsi.j
    cJ
    cA
    eltpsi.u
    toptopon
    mpbi
    cA
    cJ
    cK
    eltpsi.k
    eltpsg
    ax-mp
end
