include "cvv.mm"
include "wcel.mm"
include "csuc.mm"
include "cfv.mm"
include "cuni.mm"
include "wceq.mm"
include "com.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "frsuc.mm"
include "fvex.mm"
include "unieq.mm"
include "cbvmptv.mm"
include "uniex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "adantl.mm"
include "itunifval.mm"
include "fveq1d.mm"
include "adantr.mm"
include "unieqd.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "uni0.mm"
include "eqcomi.mm"
include "cdm.mm"
include "wfn.mm"
include "itunifn.mm"
include "fndm.mm"
include "syl.mm"
include "eleq2d.mm"
include "peano2b.mm"
include "syl6bbr.mm"
include "notbid.mm"
include "biimpar.mm"
include "ndmfv.mm"
include "3eqtr4a.mm"
include "pm2.61dan.mm"
include "0fv.mm"
include "unieqi.mm"
include "3eqtr4ri.mm"
include "fvprc.mm"
include "pm2.61i.mm"

theorem itunisuc
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cU: class U
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume ituni.u: |- U = ( x e. _V |-> ( rec ( ( y e. _V |-> U. y ) , x ) |` _om ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint d x
  disjoint d y
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  assert |- ( ( U ` A ) ` suc B ) = U. ( ( U ` A ) ` B )

  proof
    cA
    cvv
    wcel
    #
    cB
    csuc
    #
    cA
    cU
    cfv
    #
    cfv
    #
    cB
    @2
    cfv
    #
    cuni
    #
    wceq
    #
    @0
    cB
    com
    wcel
    #
    @6
    @0
    @7
    wa
    #
    @1
    vy
    cvv
    vy
    cv
    #
    cuni
    #
    cmpt
    #
    cA
    crdg
    com
    cres
    #
    cfv
    #
    cB
    @12
    cfv
    #
    cuni
    #
    @3
    @5
    @7
    @13
    @15
    wceq
    @0
    @7
    @13
    @14
    @11
    cfv
    #
    @15
    cA
    cB
    @11
    frsuc
    @14
    cvv
    wcel
    @16
    @15
    wceq
    cB
    @12
    fvex
    #
    va
    @14
    va
    cv
    #
    cuni
    #
    @15
    cvv
    @11
    @18
    @14
    unieq
    vy
    va
    cvv
    @10
    @19
    @9
    @18
    unieq
    cbvmptv
    @14
    @17
    uniex
    fvmpt
    ax-mp
    syl6eq
    adantl
    @0
    @3
    @13
    wceq
    @7
    @0
    @1
    @2
    @12
    vx
    vy
    cA
    cU
    cvv
    ituni.u
    itunifval
    #
    fveq1d
    adantr
    @8
    @4
    @14
    @0
    @4
    @14
    wceq
    @7
    @0
    cB
    @2
    @12
    @20
    fveq1d
    adantr
    unieqd
    3eqtr4d
    @0
    @7
    wn
    #
    wa
    #
    c0
    c0
    cuni
    #
    @3
    @5
    @23
    c0
    uni0
    eqcomi
    @22
    @1
    @2
    cdm
    #
    wcel
    #
    wn
    #
    @3
    c0
    wceq
    @0
    @26
    @21
    @0
    @25
    @7
    @0
    @25
    @1
    com
    wcel
    @7
    @0
    @24
    com
    @1
    @0
    @2
    com
    wfn
    @24
    com
    wceq
    vx
    vy
    cA
    cU
    cvv
    ituni.u
    itunifn
    com
    @2
    fndm
    syl
    #
    eleq2d
    cB
    peano2b
    syl6bbr
    notbid
    biimpar
    @1
    @2
    ndmfv
    syl
    @22
    @4
    c0
    @22
    cB
    @24
    wcel
    #
    wn
    #
    @4
    c0
    wceq
    @0
    @29
    @21
    @0
    @28
    @7
    @0
    @24
    com
    cB
    @27
    eleq2d
    notbid
    biimpar
    cB
    @2
    ndmfv
    syl
    unieqd
    3eqtr4a
    pm2.61dan
    @0
    wn
    #
    @1
    c0
    cfv
    #
    cB
    c0
    cfv
    #
    cuni
    #
    @3
    @5
    @23
    c0
    @33
    @31
    uni0
    @32
    c0
    cB
    0fv
    unieqi
    @1
    0fv
    3eqtr4ri
    @30
    @1
    @2
    c0
    cA
    cU
    fvprc
    #
    fveq1d
    @30
    @4
    @32
    @30
    cB
    @2
    c0
    @34
    fveq1d
    unieqd
    3eqtr4a
    pm2.61i
end
