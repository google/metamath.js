include "cioo.mm"
include "crn.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cxr.mm"
include "wrex.mm"
include "wn.mm"
include "wi.mm"
include "cxp.mm"
include "cr.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "wa.mm"
include "wne.mm"
include "cop.mm"
include "ioorinv2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "df-ne.mm"
include "neeq1.mm"
include "syl5bbr.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "cc0.mm"
include "clt.mm"
include "cinf.mm"
include "csup.mm"
include "cif.mm"
include "ioorebas.mm"
include "ioorval.mm"
include "ax-mp.mm"
include "iooid.mm"
include "iftruei.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "eqeq2i.mm"
include "biimpri.mm"
include "3eqtr4a.mm"
include "pm2.61d2.mm"

theorem ioorinv
  let vx: setvar x
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  assume ioorf.1: |- F = ( x e. ran (,) |-> if ( x = (/) , <. 0 , 0 >. , <. inf ( x , RR* , < ) , sup ( x , RR* , < ) >. ) )

  disjoint A x
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F a
  disjoint F b
  assert |- ( A e. ran (,) -> ( (,) ` ( F ` A ) ) = A )

  proof
    cA
    cioo
    crn
    #
    wcel
    #
    cA
    c0
    wceq
    #
    cA
    cF
    cfv
    #
    cioo
    cfv
    #
    cA
    wceq
    #
    @1
    cA
    va
    cv
    #
    vb
    cv
    #
    cioo
    co
    #
    wceq
    #
    vb
    cxr
    wrex
    va
    cxr
    wrex
    #
    @2
    wn
    #
    @5
    wi
    #
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    cioo
    @13
    wfn
    @1
    @10
    wb
    ioof
    @13
    @14
    cioo
    ffn
    va
    vb
    cxr
    cxr
    cA
    cioo
    ovelrn
    mp2b
    @9
    @12
    va
    vb
    cxr
    cxr
    @9
    @12
    wi
    @6
    cxr
    wcel
    @7
    cxr
    wcel
    wa
    @9
    @12
    @8
    c0
    wne
    #
    @8
    cF
    cfv
    #
    cioo
    cfv
    #
    @8
    wceq
    #
    wi
    @15
    @17
    @6
    @7
    cop
    #
    cioo
    cfv
    @8
    @15
    @16
    @19
    cioo
    vx
    @6
    @7
    cF
    ioorf.1
    ioorinv2
    fveq2d
    @6
    @7
    cioo
    df-ov
    syl6eqr
    @9
    @11
    @15
    @5
    @18
    @11
    cA
    c0
    wne
    @9
    @15
    cA
    c0
    df-ne
    cA
    @8
    c0
    neeq1
    syl5bbr
    @9
    @4
    @17
    cA
    @8
    @9
    @3
    @16
    cioo
    cA
    @8
    cF
    fveq2
    fveq2d
    @9
    id
    eqeq12d
    imbi12d
    mpbiri
    a1i
    rexlimivv
    sylbi
    @2
    cc0
    cc0
    cioo
    co
    #
    cF
    cfv
    #
    cioo
    cfv
    #
    @20
    @4
    cA
    @22
    cc0
    cc0
    cop
    #
    cioo
    cfv
    @20
    @21
    @23
    cioo
    @21
    @20
    c0
    wceq
    #
    @23
    @20
    cxr
    clt
    cinf
    @20
    cxr
    clt
    csup
    cop
    #
    cif
    #
    @23
    @20
    @0
    wcel
    @21
    @26
    wceq
    cc0
    cc0
    ioorebas
    vx
    @20
    cF
    ioorf.1
    ioorval
    ax-mp
    @24
    @23
    @25
    cc0
    iooid
    #
    iftruei
    eqtri
    fveq2i
    cc0
    cc0
    cioo
    df-ov
    eqtr4i
    @2
    @3
    @21
    cioo
    @2
    cA
    @20
    cF
    cA
    @20
    wceq
    @2
    @20
    c0
    cA
    @27
    eqeq2i
    biimpri
    #
    fveq2d
    fveq2d
    @28
    3eqtr4a
    pm2.61d2
end
