include "wfn.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cshi.mm"
include "co.mm"
include "wfun.mm"
include "cdm.mm"
include "cv.mm"
include "cmin.mm"
include "crab.mm"
include "wceq.mm"
include "wbr.mm"
include "copab.mm"
include "wrel.mm"
include "wmo.mm"
include "wal.mm"
include "relopab.mm"
include "a1i.mm"
include "fnfun.mm"
include "adantr.mm"
include "funmo.mm"
include "vex.mm"
include "eleq1.mm"
include "oveq1.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "breq2.mm"
include "anbi2d.mm"
include "eqid.mm"
include "brab.mm"
include "simprbi.mm"
include "moimi.mm"
include "syl.mm"
include "alrimiv.mm"
include "dffun6.mm"
include "sylanbrc.mm"
include "shftfval.mm"
include "adantl.mm"
include "funeqd.mm"
include "mpbird.mm"
include "shftdm.mm"
include "fndm.mm"
include "eleq2d.mm"
include "rabbidv.mm"
include "sylan9eqr.mm"
include "df-fn.mm"

theorem shftfn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume shftfval.1: |- F e. _V

  disjoint A x
  disjoint F x
  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint B w
  disjoint B y
  disjoint B z
  assert |- ( ( F Fn B /\ A e. CC ) -> ( F shift A ) Fn { x e. CC | ( x - A ) e. B } )

  proof
    cF
    cB
    wfn
    #
    cA
    cc
    wcel
    #
    wa
    #
    cF
    cA
    cshi
    co
    #
    wfun
    #
    @3
    cdm
    #
    vx
    cv
    #
    cA
    cmin
    co
    #
    cB
    wcel
    #
    vx
    cc
    crab
    #
    wceq
    @3
    @9
    wfn
    @2
    @4
    @6
    cc
    wcel
    #
    @7
    vy
    cv
    #
    cF
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    wfun
    #
    @2
    @14
    wrel
    #
    vz
    cv
    #
    vw
    cv
    #
    @14
    wbr
    #
    vw
    wmo
    #
    vz
    wal
    #
    @15
    @16
    @2
    @13
    vx
    vy
    relopab
    a1i
    @2
    cF
    wfun
    #
    @21
    @0
    @22
    @1
    cB
    cF
    fnfun
    adantr
    @22
    @20
    vz
    @22
    @17
    cA
    cmin
    co
    #
    @18
    cF
    wbr
    #
    vw
    wmo
    @20
    vw
    @23
    cF
    funmo
    @19
    @24
    vw
    @19
    @17
    cc
    wcel
    #
    @24
    @13
    @25
    @23
    @11
    cF
    wbr
    #
    wa
    @25
    @24
    wa
    vx
    vy
    @17
    @18
    @14
    vz
    vex
    vw
    vex
    @6
    @17
    wceq
    #
    @10
    @25
    @12
    @26
    @6
    @17
    cc
    eleq1
    @27
    @7
    @23
    @11
    cF
    @6
    @17
    cA
    cmin
    oveq1
    breq1d
    anbi12d
    @11
    @18
    wceq
    @26
    @24
    @25
    @11
    @18
    @23
    cF
    breq2
    anbi2d
    @14
    eqid
    brab
    simprbi
    moimi
    syl
    alrimiv
    syl
    vz
    vw
    @14
    dffun6
    sylanbrc
    @2
    @3
    @14
    @1
    @3
    @14
    wceq
    @0
    vx
    vy
    cA
    cF
    shftfval.1
    shftfval
    adantl
    funeqd
    mpbird
    @1
    @0
    @5
    @7
    cF
    cdm
    #
    wcel
    #
    vx
    cc
    crab
    @9
    vx
    cA
    cF
    shftfval.1
    shftdm
    @0
    @29
    @8
    vx
    cc
    @0
    @28
    cB
    @7
    cB
    cF
    fndm
    eleq2d
    rabbidv
    sylan9eqr
    @3
    @9
    df-fn
    sylanbrc
end
