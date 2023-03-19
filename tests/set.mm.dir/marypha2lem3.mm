include "wfn.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "copab.mm"
include "cmpt.mm"
include "dffn5.mm"
include "biimpi.mm"
include "adantl.mm"
include "df-mpt.mm"
include "syl6eq.mm"
include "marypha2lem2.mm"
include "a1i.mm"
include "sseq12d.mm"
include "ssopab2b.mm"
include "syl6bb.mm"
include "19.21v.mm"
include "imdistan.mm"
include "albii.mm"
include "fvex.mm"
include "eleq1.mm"
include "ceqsalv.mm"
include "imbi2i.mm"
include "3bitr3i.mm"
include "df-ral.mm"
include "bitr4i.mm"

theorem marypha2lem3
  let vx: setvar x
  let cA: class A
  let cT: class T
  let cF: class F
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume marypha2lem.t: |- T = U_ x e. A ( { x } X. ( F ` x ) )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint X x
  disjoint X y
  assert |- ( ( F Fn A /\ G Fn A ) -> ( G C_ T <-> A. x e. A ( G ` x ) e. ( F ` x ) ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cA
    wfn
    #
    wa
    #
    cG
    cT
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    @4
    cG
    cfv
    #
    wceq
    #
    wa
    #
    @5
    @6
    @4
    cF
    cfv
    #
    wcel
    #
    wa
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @7
    @10
    wcel
    #
    vx
    cA
    wral
    #
    @2
    @3
    @9
    vx
    vy
    copab
    #
    @12
    vx
    vy
    copab
    #
    wss
    @15
    @2
    cG
    @18
    cT
    @19
    @2
    cG
    vx
    cA
    @7
    cmpt
    #
    @18
    @1
    cG
    @20
    wceq
    #
    @0
    @1
    @21
    vx
    cA
    cG
    dffn5
    biimpi
    adantl
    vx
    vy
    cA
    @7
    df-mpt
    syl6eq
    cT
    @19
    wceq
    @2
    vx
    vy
    cA
    cT
    cF
    marypha2lem.t
    marypha2lem2
    a1i
    sseq12d
    @9
    @12
    vx
    vy
    ssopab2b
    syl6bb
    @15
    @5
    @16
    wi
    #
    vx
    wal
    @17
    @14
    @22
    vx
    @5
    @8
    @11
    wi
    #
    wi
    #
    vy
    wal
    @5
    @23
    vy
    wal
    #
    wi
    @14
    @22
    @5
    @23
    vy
    19.21v
    @24
    @13
    vy
    @5
    @8
    @11
    imdistan
    albii
    @25
    @16
    @5
    @11
    @16
    vy
    @7
    @4
    cG
    fvex
    @6
    @7
    @10
    eleq1
    ceqsalv
    imbi2i
    3bitr3i
    albii
    @16
    vx
    cA
    df-ral
    bitr4i
    syl6bb
end
