include "ccoda.mm"
include "cres.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "wss.mm"
include "c2nd.mm"
include "c1st.mm"
include "ccom.mm"
include "wfo.mm"
include "fo2nd.mm"
include "fofn.mm"
include "ax-mp.mm"
include "fo1st.mm"
include "fof.mm"
include "fnfco.mm"
include "mp2an.mm"
include "df-coda.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "ssv.mm"
include "fnssres.mm"
include "fvres.mm"
include "arwcd.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem cdaf
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cH: class H
  assume arwrcl.a: |- A = ( Arrow ` C )
  assume arwdm.b: |- B = ( Base ` C )


  assert |- ( codA |` A ) : A --> B

  proof
    cA
    cB
    ccoda
    cA
    cres
    #
    wf
    @0
    cA
    wfn
    #
    vx
    cv
    #
    @0
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    ccoda
    cvv
    wfn
    #
    cA
    cvv
    wss
    @1
    @5
    c2nd
    c1st
    ccom
    #
    cvv
    wfn
    #
    c2nd
    cvv
    wfn
    #
    cvv
    cvv
    c1st
    wf
    #
    @7
    cvv
    cvv
    c2nd
    wfo
    @8
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    ax-mp
    cvv
    cvv
    c1st
    wfo
    @9
    fo1st
    cvv
    cvv
    c1st
    fof
    ax-mp
    cvv
    cvv
    c2nd
    c1st
    fnfco
    mp2an
    cvv
    ccoda
    @6
    df-coda
    fneq1i
    mpbir
    cA
    ssv
    cvv
    cA
    ccoda
    fnssres
    mp2an
    @4
    vx
    cA
    @2
    cA
    wcel
    @3
    @2
    ccoda
    cfv
    cB
    @2
    cA
    ccoda
    fvres
    cA
    cB
    cC
    @2
    arwrcl.a
    arwdm.b
    arwcd
    eqeltrd
    rgen
    vx
    cA
    cB
    @0
    ffnfv
    mpbir2an
end
