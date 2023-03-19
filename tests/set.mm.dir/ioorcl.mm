include "cioo.mm"
include "crn.mm"
include "wcel.mm"
include "covol.mm"
include "cfv.mm"
include "cr.mm"
include "wa.mm"
include "cle.mm"
include "cxp.mm"
include "cxr.mm"
include "cin.mm"
include "inss1.mm"
include "ioorf.mm"
include "ffvelrni.mm"
include "adantr.mm"
include "sseldi.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cop.mm"
include "clt.mm"
include "cinf.mm"
include "csup.mm"
include "cif.mm"
include "ioorval.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "0re.mm"
include "opelxpi.mm"
include "mp2an.mm"
include "syl6eqel.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wi.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "ioorinv2.mm"
include "adantl.mm"
include "ioorcl2.mm"
include "ancoms.mm"
include "syl.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "impl.mm"
include "pm2.61dane.mm"
include "elind.mm"

theorem ioorcl
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
  assert |- ( ( A e. ran (,) /\ ( vol* ` A ) e. RR ) -> ( F ` A ) e. ( <_ i^i ( RR X. RR ) ) )

  proof
    cA
    cioo
    crn
    #
    wcel
    #
    cA
    covol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    cle
    cr
    cr
    cxp
    #
    cA
    cF
    cfv
    #
    @4
    cle
    cxr
    cxr
    cxp
    #
    cin
    #
    cle
    @6
    cle
    @7
    inss1
    @1
    @6
    @8
    wcel
    @3
    @0
    @8
    cA
    cF
    vx
    cF
    ioorf.1
    ioorf
    ffvelrni
    adantr
    sseldi
    @4
    @6
    @5
    wcel
    #
    cA
    c0
    @4
    cA
    c0
    wceq
    #
    wa
    @6
    cc0
    cc0
    cop
    #
    @5
    @4
    @10
    @6
    @10
    @11
    cA
    cxr
    clt
    cinf
    cA
    cxr
    clt
    csup
    cop
    #
    cif
    #
    @11
    @1
    @6
    @13
    wceq
    @3
    vx
    cA
    cF
    ioorf.1
    ioorval
    adantr
    @10
    @11
    @12
    iftrue
    sylan9eq
    cc0
    cr
    wcel
    #
    @14
    @11
    @5
    wcel
    0re
    0re
    cc0
    cc0
    cr
    cr
    opelxpi
    mp2an
    syl6eqel
    @1
    @3
    cA
    c0
    wne
    #
    @9
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
    @3
    @15
    wa
    #
    @9
    wi
    #
    @7
    cr
    cpw
    #
    cioo
    wf
    cioo
    @7
    wfn
    @1
    @20
    wb
    ioof
    @7
    @23
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
    @19
    @22
    va
    vb
    cxr
    cxr
    @19
    @22
    wi
    @16
    cxr
    wcel
    @17
    cxr
    wcel
    wa
    @19
    @22
    @18
    covol
    cfv
    #
    cr
    wcel
    #
    @18
    c0
    wne
    #
    wa
    #
    @18
    cF
    cfv
    #
    @5
    wcel
    #
    wi
    @27
    @28
    @16
    @17
    cop
    #
    @5
    @26
    @28
    @30
    wceq
    @25
    vx
    @16
    @17
    cF
    ioorf.1
    ioorinv2
    adantl
    @27
    @16
    cr
    wcel
    @17
    cr
    wcel
    wa
    #
    @30
    @5
    wcel
    @26
    @25
    @31
    @16
    @17
    ioorcl2
    ancoms
    @16
    @17
    cr
    cr
    opelxpi
    syl
    eqeltrd
    @19
    @21
    @27
    @9
    @29
    @19
    @3
    @25
    @15
    @26
    @19
    @2
    @24
    cr
    cA
    @18
    covol
    fveq2
    eleq1d
    cA
    @18
    c0
    neeq1
    anbi12d
    @19
    @6
    @28
    @5
    cA
    @18
    cF
    fveq2
    eleq1d
    imbi12d
    mpbiri
    a1i
    rexlimivv
    sylbi
    impl
    pm2.61dane
    elind
end
