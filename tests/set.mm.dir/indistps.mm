include "c0.mm"
include "cpr.mm"
include "cuni.mm"
include "cun.mm"
include "0ex.mm"
include "unipr.mm"
include "uncom.mm"
include "un0.mm"
include "3eqtrri.mm"
include "indistop.mm"
include "eltpsi.mm"

theorem indistps
  let cA: class A
  let cK: class K
  assume indistps.a: |- A e. _V
  assume indistps.k: |- K = { <. ( Base ` ndx ) , A >. , <. ( TopSet ` ndx ) , { (/) , A } >. }


  assert |- K e. TopSp

  proof
    cA
    c0
    cA
    cpr
    #
    cK
    indistps.k
    @0
    cuni
    c0
    cA
    cun
    cA
    c0
    cun
    cA
    c0
    cA
    0ex
    indistps.a
    unipr
    c0
    cA
    uncom
    cA
    un0
    3eqtrri
    cA
    indistop
    eltpsi
end
