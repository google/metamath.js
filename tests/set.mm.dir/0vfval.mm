include "wcel.mm"
include "cvv.mm"
include "cgi.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "cpv.mm"
include "ccom.mm"
include "wfn.mm"
include "c1st.mm"
include "crn.mm"
include "wss.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "ssv.mm"
include "fnco.mm"
include "mp3an.mm"
include "df-va.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fvco2.mm"
include "mpan.mm"
include "cn0v.mm"
include "df-0v.mm"
include "fveq1i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "syl.mm"

theorem 0vfval
  let cU: class U
  let cG: class G
  let cV: class V
  let cZ: class Z
  assume 0vfval.2: |- G = ( +v ` U )
  assume 0vfval.5: |- Z = ( 0vec ` U )


  assert |- ( U e. V -> Z = ( GId ` G ) )

  proof
    cU
    cV
    wcel
    cU
    cvv
    wcel
    #
    cZ
    cG
    cgi
    cfv
    #
    wceq
    cU
    cV
    elex
    @0
    cU
    cgi
    cpv
    ccom
    #
    cfv
    #
    cU
    cpv
    cfv
    #
    cgi
    cfv
    #
    cZ
    @1
    cpv
    cvv
    wfn
    #
    @0
    @3
    @5
    wceq
    @6
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
    @9
    c1st
    crn
    #
    cvv
    wss
    @8
    cvv
    cvv
    c1st
    wfo
    @9
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    #
    @11
    @10
    ssv
    cvv
    cvv
    c1st
    c1st
    fnco
    mp3an
    cvv
    cpv
    @7
    df-va
    fneq1i
    mpbir
    cvv
    cgi
    cpv
    cU
    fvco2
    mpan
    cZ
    cU
    cn0v
    cfv
    @3
    0vfval.5
    cU
    cn0v
    @2
    df-0v
    fveq1i
    eqtri
    cG
    @4
    cgi
    0vfval.2
    fveq2i
    3eqtr4g
    syl
end
