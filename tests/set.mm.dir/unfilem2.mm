include "coa.mm"
include "co.mm"
include "cdif.mm"
include "wf1o.mm"
include "wf1.mm"
include "wfo.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wfn.mm"
include "crn.mm"
include "ovex.mm"
include "fnmpti.mm"
include "unfilem1.mm"
include "df-fo.mm"
include "mpbir2an.mm"
include "fof.mm"
include "ax-mp.mm"
include "wcel.mm"
include "wa.mm"
include "oveq2.mm"
include "fvmpt.mm"
include "eqeqan12d.mm"
include "com.mm"
include "wb.mm"
include "elnn.mm"
include "mpan2.mm"
include "nnacan.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "bitrd.mm"
include "biimpd.mm"
include "rgen2a.mm"
include "dff13.mm"
include "df-f1o.mm"

theorem unfilem2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume unfilem1.1: |- A e. _om
  assume unfilem1.2: |- B e. _om
  assume unfilem1.3: |- F = ( x e. B |-> ( A +o x ) )

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F w
  disjoint F y
  disjoint F z
  assert |- F : B -1-1-onto-> ( ( A +o B ) \ A )

  proof
    cB
    cA
    cB
    coa
    co
    cA
    cdif
    #
    cF
    wf1o
    cB
    @0
    cF
    wf1
    #
    cB
    @0
    cF
    wfo
    #
    @1
    cB
    @0
    cF
    wf
    #
    vz
    cv
    #
    cF
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @4
    @6
    wceq
    #
    wi
    #
    vw
    cB
    wral
    vz
    cB
    wral
    @2
    @3
    @2
    cF
    cB
    wfn
    cF
    crn
    @0
    wceq
    vx
    cB
    cA
    vx
    cv
    #
    coa
    co
    #
    cF
    cA
    @11
    coa
    ovex
    unfilem1.3
    fnmpti
    vx
    cA
    cB
    cF
    unfilem1.1
    unfilem1.2
    unfilem1.3
    unfilem1
    cB
    @0
    cF
    df-fo
    mpbir2an
    #
    cB
    @0
    cF
    fof
    ax-mp
    @10
    vz
    vw
    cB
    @4
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    wa
    #
    @8
    @9
    @16
    @8
    cA
    @4
    coa
    co
    #
    cA
    @6
    coa
    co
    #
    wceq
    #
    @9
    @14
    @15
    @5
    @17
    @7
    @18
    vx
    @4
    @12
    @17
    cB
    cF
    @11
    @4
    cA
    coa
    oveq2
    unfilem1.3
    cA
    @4
    coa
    ovex
    fvmpt
    vx
    @6
    @12
    @18
    cB
    cF
    @11
    @6
    cA
    coa
    oveq2
    unfilem1.3
    cA
    @6
    coa
    ovex
    fvmpt
    eqeqan12d
    @14
    @4
    com
    wcel
    #
    @6
    com
    wcel
    #
    @19
    @9
    wb
    #
    @15
    @14
    cB
    com
    wcel
    #
    @20
    unfilem1.2
    @4
    cB
    elnn
    mpan2
    @15
    @23
    @21
    unfilem1.2
    @6
    cB
    elnn
    mpan2
    cA
    com
    wcel
    @20
    @21
    @22
    unfilem1.1
    cA
    @4
    @6
    nnacan
    mp3an1
    syl2an
    bitrd
    biimpd
    rgen2a
    vz
    vw
    cB
    @0
    cF
    dff13
    mpbir2an
    @13
    cB
    @0
    cF
    df-f1o
    mpbir2an
end
