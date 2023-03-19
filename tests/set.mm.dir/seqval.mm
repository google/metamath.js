include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt2.mm"
include "crdg.mm"
include "com.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "cseq.mm"
include "df-ima.mm"
include "df-seq.mm"
include "wceq.mm"
include "eqid.mm"
include "wcel.mm"
include "vex.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "mp2an.mm"
include "opeq2i.mm"
include "mpt2eq123i.mm"
include "rdgeq1.mm"
include "ax-mp.mm"
include "reseq1i.mm"
include "eqtri.mm"
include "rneqi.mm"
include "3eqtr4i.mm"

theorem seqval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let c.pl: class .+
  let cR: class R
  let cF: class F
  let cM: class M
  assume seqval.1: |- R = ( rec ( ( x e. _V , y e. _V |-> <. ( x + 1 ) , ( x ( z e. _V , w e. _V |-> ( w .+ ( F ` ( z + 1 ) ) ) ) y ) >. ) , <. M , ( F ` M ) >. ) |` _om )

  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .+ w
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint M x
  disjoint M y
  assert |- seq M ( .+ , F ) = ran R

  proof
    vx
    vy
    cvv
    cvv
    vx
    cv
    #
    c1
    caddc
    co
    #
    vy
    cv
    #
    @1
    cF
    cfv
    #
    c.pl
    co
    #
    cop
    #
    cmpt2
    #
    cM
    cM
    cF
    cfv
    cop
    #
    crdg
    #
    com
    cima
    @8
    com
    cres
    #
    crn
    c.pl
    cF
    cM
    cseq
    cR
    crn
    @8
    com
    df-ima
    vx
    vy
    c.pl
    cF
    cM
    df-seq
    cR
    @9
    cR
    vx
    vy
    cvv
    cvv
    @1
    @0
    @2
    vz
    vw
    cvv
    cvv
    vw
    cv
    #
    vz
    cv
    #
    c1
    caddc
    co
    #
    cF
    cfv
    #
    c.pl
    co
    #
    cmpt2
    #
    co
    #
    cop
    #
    cmpt2
    #
    @7
    crdg
    #
    com
    cres
    @9
    seqval.1
    @19
    @8
    com
    @18
    @6
    wceq
    @19
    @8
    wceq
    vx
    vy
    cvv
    cvv
    @17
    cvv
    cvv
    @5
    cvv
    eqid
    #
    @20
    @16
    @4
    @1
    @0
    cvv
    wcel
    @2
    cvv
    wcel
    @16
    @4
    wceq
    vx
    vex
    vy
    vex
    vz
    vw
    @0
    @2
    cvv
    cvv
    @14
    @4
    @15
    @10
    @3
    c.pl
    co
    @11
    @0
    wceq
    #
    @13
    @3
    @10
    c.pl
    @21
    @12
    @1
    cF
    @11
    @0
    c1
    caddc
    oveq1
    fveq2d
    oveq2d
    @10
    @2
    @3
    c.pl
    oveq1
    @15
    eqid
    @2
    @3
    c.pl
    ovex
    ovmpt2
    mp2an
    opeq2i
    mpt2eq123i
    @7
    @18
    @6
    rdgeq1
    ax-mp
    reseq1i
    eqtri
    rneqi
    3eqtr4i
end
