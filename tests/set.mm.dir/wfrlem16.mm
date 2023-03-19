include "cdm.mm"
include "wfrdmss.mm"
include "wss.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cpred.mm"
include "wrex.mm"
include "wcel.mm"
include "eldifn.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "ssun2.mm"
include "vsnid.mm"
include "sselii.mm"
include "cres.mm"
include "cfv.mm"
include "cop.mm"
include "dmeqi.mm"
include "dmun.mm"
include "fvex.mm"
include "dmsnop.mm"
include "uneq2i.mm"
include "3eqtri.mm"
include "eleqtrri.mm"
include "wfn.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "cuni.mm"
include "wfrlem15.mm"
include "elssuni.mm"
include "syl.mm"
include "cwrecs.mm"
include "df-wrecs.mm"
include "eqtri.mm"
include "syl6sseqr.mm"
include "dmss.mm"
include "sseld.mm"
include "mpi.mm"
include "mtand.mm"
include "nrex.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "difss.mm"
include "tz6.26i.mm"
include "mpan.mm"
include "sylbir.mm"
include "mt3.mm"
include "ssdif0.mm"
include "mpbir.mm"
include "eqssi.mm"

theorem wfrlem16
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume wfrlem13.1: |- R We A
  assume wfrlem13.2: |- R Se A
  assume wfrlem13.3: |- F = wrecs ( R , A , G )
  assume wfrlem13.4: |- C = ( F u. { <. z , ( G ` ( F |` Pred ( R , A , z ) ) ) >. } )

  disjoint A z
  disjoint F z
  disjoint R z
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint C f
  disjoint C x
  disjoint C y
  assert |- dom F = A

  proof
    cF
    cdm
    #
    cA
    cA
    cR
    cF
    cG
    wfrlem13.3
    wfrdmss
    cA
    @0
    wss
    cA
    @0
    cdif
    #
    c0
    wceq
    #
    @2
    @1
    cR
    vz
    cv
    #
    cpred
    c0
    wceq
    #
    vz
    @1
    wrex
    #
    @4
    vz
    @1
    @3
    @1
    wcel
    #
    @4
    @3
    @0
    wcel
    #
    @3
    cA
    @0
    eldifn
    @6
    @4
    wa
    #
    @3
    cC
    cdm
    #
    wcel
    @7
    @3
    @0
    @3
    csn
    #
    cun
    #
    @9
    @10
    @11
    @3
    @10
    @0
    ssun2
    vz
    vsnid
    sselii
    @9
    cF
    @3
    cF
    cA
    cR
    @3
    cpred
    cres
    #
    cG
    cfv
    #
    cop
    csn
    #
    cun
    #
    cdm
    @0
    @14
    cdm
    #
    cun
    @11
    cC
    @15
    wfrlem13.4
    dmeqi
    cF
    @14
    dmun
    @16
    @10
    @0
    @3
    @13
    @12
    cG
    fvex
    dmsnop
    uneq2i
    3eqtri
    eleqtrri
    @8
    @9
    @0
    @3
    @8
    cC
    cF
    wss
    @9
    @0
    wss
    @8
    cC
    vf
    cv
    #
    vx
    cv
    #
    wfn
    @18
    cA
    wss
    cA
    cR
    vy
    cv
    #
    cpred
    #
    @18
    wss
    vy
    @18
    wral
    wa
    @19
    @17
    cfv
    @17
    @20
    cres
    cG
    cfv
    wceq
    vy
    @18
    wral
    w3a
    vx
    wex
    vf
    cab
    #
    cuni
    #
    cF
    @8
    cC
    @21
    wcel
    cC
    @22
    wss
    vx
    vy
    vz
    cA
    cC
    cR
    vf
    cF
    cG
    wfrlem13.1
    wfrlem13.2
    wfrlem13.3
    wfrlem13.4
    wfrlem15
    cC
    @21
    elssuni
    syl
    cF
    cA
    cR
    cG
    cwrecs
    @22
    wfrlem13.3
    vx
    vy
    cA
    cR
    vf
    cG
    df-wrecs
    eqtri
    syl6sseqr
    cC
    cF
    dmss
    syl
    sseld
    mpi
    mtand
    nrex
    @2
    wn
    @1
    c0
    wne
    #
    @5
    @1
    c0
    df-ne
    @1
    cA
    wss
    @23
    @5
    cA
    @0
    difss
    vz
    cA
    @1
    cR
    wfrlem13.1
    wfrlem13.2
    tz6.26i
    mpan
    sylbir
    mt3
    cA
    @0
    ssdif0
    mpbir
    eqssi
end
