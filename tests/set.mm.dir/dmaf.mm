include "cdoma.mm"
include "cres.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "wss.mm"
include "c1st.mm"
include "ccom.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "fof.mm"
include "fnfco.mm"
include "mp2an.mm"
include "df-doma.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "ssv.mm"
include "fnssres.mm"
include "fvres.mm"
include "arwdm.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem dmaf
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


  assert |- ( domA |` A ) : A --> B

  proof
    cA
    cB
    cdoma
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
    cdoma
    cvv
    wfn
    #
    cA
    cvv
    wss
    @1
    @5
    c1st
    c1st
    ccom
    #
    cvv
    wfn
    #
    c1st
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
    c1st
    wfo
    #
    @8
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    @10
    @9
    fo1st
    cvv
    cvv
    c1st
    fof
    ax-mp
    cvv
    cvv
    c1st
    c1st
    fnfco
    mp2an
    cvv
    cdoma
    @6
    df-doma
    fneq1i
    mpbir
    cA
    ssv
    cvv
    cA
    cdoma
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
    cdoma
    cfv
    cB
    @2
    cA
    cdoma
    fvres
    cA
    cB
    cC
    @2
    arwrcl.a
    arwdm.b
    arwdm
    eqeltrd
    rgen
    vx
    cA
    cB
    @0
    ffnfv
    mpbir2an
end
