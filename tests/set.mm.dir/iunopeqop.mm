include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wrex.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "wo.mm"
include "cop.mm"
include "ciun.mm"
include "wi.mm"
include "n0snor2el.mm"
include "nfiu1.mm"
include "nfeq1.mm"
include "nfv.mm"
include "nfim.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "csb.mm"
include "ssiun2.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfop.mm"
include "nfsn.mm"
include "nfss.mm"
include "id.mm"
include "csbeq1a.mm"
include "opeq12d.mm"
include "sneqd.mm"
include "sseq1d.mm"
include "vtoclgaf.mm"
include "anim12i.mm"
include "cun.mm"
include "unss.mm"
include "sseq2.mm"
include "cpr.mm"
include "df-pr.mm"
include "eqcomi.mm"
include "sseq1i.mm"
include "vex.mm"
include "csbex.mm"
include "propssopi.mm"
include "eqneqall.mm"
include "syl.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "com14.mm"
include "syl5bi.mm"
include "mpd.mm"
include "rexlimdva.mm"
include "rexlimi.mm"
include "ax-1.mm"
include "jaoi.mm"

theorem iunopeqop
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  assume iunopeqop.b: |- B e. _V
  assume iunopeqop.c: |- C e. _V
  assume iunopeqop.d: |- D e. _V

  disjoint A x
  disjoint A z
  disjoint x z
  disjoint C x
  disjoint D x
  disjoint A y
  disjoint x y
  disjoint y z
  disjoint B y
  disjoint C y
  disjoint D y
  assert |- ( A =/= (/) -> ( U_ x e. A { <. x , B >. } = <. C , D >. -> E. z A = { z } ) )

  proof
    cA
    c0
    wne
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wrex
    #
    cA
    vz
    cv
    csn
    wceq
    vz
    wex
    #
    wo
    vx
    cA
    @0
    cB
    cop
    #
    csn
    #
    ciun
    #
    cC
    cD
    cop
    #
    wceq
    #
    @5
    wi
    #
    vx
    vy
    vz
    cA
    n0snor2el
    @4
    @11
    @5
    @3
    @11
    vx
    cA
    @10
    @5
    vx
    vx
    @8
    @9
    vx
    cA
    @7
    nfiu1
    #
    nfeq1
    @5
    vx
    nfv
    nfim
    @0
    cA
    wcel
    #
    @2
    @11
    vy
    cA
    @13
    @1
    cA
    wcel
    #
    wa
    #
    @7
    @8
    wss
    #
    @1
    vx
    @1
    cB
    csb
    #
    cop
    #
    csn
    #
    @8
    wss
    #
    wa
    #
    @2
    @11
    wi
    #
    @13
    @16
    @14
    @20
    vx
    cA
    @7
    ssiun2
    #
    @16
    @20
    vx
    @1
    cA
    vx
    @1
    nfcv
    #
    vx
    @19
    @8
    vx
    @18
    vx
    @1
    @17
    @24
    vx
    @1
    cB
    nfcsb1v
    nfop
    nfsn
    @12
    nfss
    @0
    @1
    wceq
    #
    @7
    @19
    @8
    @25
    @6
    @18
    @25
    @0
    @1
    cB
    @17
    @25
    id
    vx
    @1
    cB
    csbeq1a
    opeq12d
    sneqd
    sseq1d
    @23
    vtoclgaf
    anim12i
    @21
    @7
    @19
    cun
    #
    @8
    wss
    #
    @15
    @22
    @7
    @19
    @8
    unss
    @10
    @27
    @2
    @15
    @5
    @10
    @27
    @26
    @9
    wss
    #
    @2
    @15
    @5
    wi
    #
    wi
    #
    @8
    @9
    @26
    sseq2
    @28
    @6
    @18
    cpr
    #
    @9
    wss
    #
    @30
    @26
    @31
    @9
    @31
    @26
    @6
    @18
    df-pr
    eqcomi
    sseq1i
    @32
    @25
    @30
    @0
    cB
    @1
    @17
    cC
    cD
    vx
    vex
    iunopeqop.b
    vy
    vex
    vx
    @1
    cB
    iunopeqop.b
    csbex
    iunopeqop.c
    iunopeqop.d
    propssopi
    @29
    @0
    @1
    eqneqall
    syl
    sylbi
    syl6bi
    com14
    syl5bi
    mpd
    rexlimdva
    rexlimi
    @5
    @10
    ax-1
    jaoi
    syl
end
