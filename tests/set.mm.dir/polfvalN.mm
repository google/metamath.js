include "wcel.mm"
include "cvv.mm"
include "cpw.mm"
include "cv.mm"
include "cfv.mm"
include "ciin.mm"
include "cin.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "cpolN.mm"
include "catm.mm"
include "coc.mm"
include "cpmap.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "fveq1d.mm"
include "fveq12d.mm"
include "adantr.mm"
include "iineq2dv.mm"
include "ineq12d.mm"
include "mpteq12dv.mm"
include "df-polarityN.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem polfvalN
  let cA: class A
  let cB: class B
  let cP: class P
  let vm: setvar m
  let cK: class K
  let cM: class M
  let c.pe: class ._|_
  let vp: setvar p
  let vh: setvar h
  assume polfval.o: |- ._|_ = ( oc ` K )
  assume polfval.a: |- A = ( Atoms ` K )
  assume polfval.m: |- M = ( pmap ` K )
  assume polfval.p: |- P = ( _|_P ` K )

  disjoint A m
  disjoint m p
  disjoint K m
  disjoint K p
  disjoint h m
  disjoint A h
  disjoint h p
  disjoint K h
  disjoint M h
  disjoint ._|_ h
  assert |- ( K e. B -> P = ( m e. ~P A |-> ( A i^i |^|_ p e. m ( M ` ( ._|_ ` p ) ) ) ) )

  proof
    cK
    cB
    wcel
    cK
    cvv
    wcel
    #
    cP
    vm
    cA
    cpw
    #
    cA
    vp
    vm
    cv
    #
    vp
    cv
    #
    c.pe
    cfv
    #
    cM
    cfv
    #
    ciin
    #
    cin
    #
    cmpt
    #
    wceq
    cK
    cB
    elex
    @0
    cP
    cK
    cpolN
    cfv
    @8
    polfval.p
    vh
    cK
    vm
    vh
    cv
    #
    catm
    cfv
    #
    cpw
    #
    @10
    vp
    @2
    @3
    @9
    coc
    cfv
    #
    cfv
    #
    @9
    cpmap
    cfv
    #
    cfv
    #
    ciin
    #
    cin
    #
    cmpt
    @8
    cvv
    cpolN
    @9
    cK
    wceq
    #
    vm
    @11
    @17
    @1
    @7
    @18
    @10
    cA
    @18
    @10
    cK
    catm
    cfv
    #
    cA
    @9
    cK
    catm
    fveq2
    polfval.a
    syl6eqr
    #
    pweqd
    @18
    @10
    cA
    @16
    @6
    @20
    @18
    vp
    @2
    @15
    @5
    @18
    @15
    @5
    wceq
    @3
    @2
    wcel
    @18
    @13
    @4
    @14
    cM
    @18
    @14
    cK
    cpmap
    cfv
    cM
    @9
    cK
    cpmap
    fveq2
    polfval.m
    syl6eqr
    @18
    @3
    @12
    c.pe
    @18
    @12
    cK
    coc
    cfv
    c.pe
    @9
    cK
    coc
    fveq2
    polfval.o
    syl6eqr
    fveq1d
    fveq12d
    adantr
    iineq2dv
    ineq12d
    mpteq12dv
    vm
    vp
    vh
    df-polarityN
    vm
    @1
    @7
    cA
    cA
    @19
    cvv
    polfval.a
    cK
    catm
    fvex
    eqeltri
    pwex
    mptex
    fvmpt
    syl5eq
    syl
end
