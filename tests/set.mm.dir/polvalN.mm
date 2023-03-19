include "wss.mm"
include "wcel.mm"
include "cpw.mm"
include "cfv.mm"
include "cv.mm"
include "ciin.mm"
include "cin.mm"
include "wceq.mm"
include "catm.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "cmpt.mm"
include "polfvalN.mm"
include "fveq1d.mm"
include "iineq1.mm"
include "ineq2d.mm"
include "eqid.mm"
include "inex1.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "sylan2br.mm"

theorem polvalN
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let vp: setvar p
  let vh: setvar h
  let vm: setvar m
  assume polfval.o: |- ._|_ = ( oc ` K )
  assume polfval.a: |- A = ( Atoms ` K )
  assume polfval.m: |- M = ( pmap ` K )
  assume polfval.p: |- P = ( _|_P ` K )

  disjoint K p
  disjoint X p
  disjoint h m
  disjoint A h
  disjoint A m
  disjoint h p
  disjoint K h
  disjoint m p
  disjoint K m
  disjoint M h
  disjoint ._|_ h
  disjoint M m
  disjoint ._|_ m
  disjoint X m
  assert |- ( ( K e. B /\ X C_ A ) -> ( P ` X ) = ( A i^i |^|_ p e. X ( M ` ( ._|_ ` p ) ) ) )

  proof
    cX
    cA
    wss
    cK
    cB
    wcel
    #
    cX
    cA
    cpw
    #
    wcel
    #
    cX
    cP
    cfv
    #
    cA
    vp
    cX
    vp
    cv
    c.pe
    cfv
    cM
    cfv
    #
    ciin
    #
    cin
    #
    wceq
    cX
    cA
    cA
    cK
    catm
    cfv
    cvv
    polfval.a
    cK
    catm
    fvex
    eqeltri
    #
    elpw2
    @0
    @2
    @3
    cX
    vm
    @1
    cA
    vp
    vm
    cv
    #
    @4
    ciin
    #
    cin
    #
    cmpt
    #
    cfv
    @6
    @0
    cX
    cP
    @11
    cA
    cB
    cP
    vm
    cK
    cM
    c.pe
    vp
    polfval.o
    polfval.a
    polfval.m
    polfval.p
    polfvalN
    fveq1d
    vm
    cX
    @10
    @6
    @1
    @11
    @8
    cX
    wceq
    @9
    @5
    cA
    vp
    @8
    cX
    @4
    iineq1
    ineq2d
    @11
    eqid
    cA
    @5
    @7
    inex1
    fvmpt
    sylan9eq
    sylan2br
end
