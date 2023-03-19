include "cns.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ccom.mm"
include "df-sm.mm"
include "fveq1i.mm"
include "wf.mm"
include "wfo.mm"
include "fo1st.mm"
include "fof.mm"
include "ax-mp.mm"
include "fvco3.mm"
include "mpan.mm"
include "syl5eq.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "fveq2d.mm"
include "2nd0.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem smfval
  let cS: class S
  let cU: class U
  assume smfval.4: |- S = ( .sOLD ` U )


  assert |- S = ( 2nd ` ( 1st ` U ) )

  proof
    cS
    cU
    cns
    cfv
    #
    cU
    c1st
    cfv
    #
    c2nd
    cfv
    #
    smfval.4
    cU
    cvv
    wcel
    #
    @0
    @2
    wceq
    @3
    @0
    cU
    c2nd
    c1st
    ccom
    #
    cfv
    #
    @2
    cU
    cns
    @4
    df-sm
    fveq1i
    cvv
    cvv
    c1st
    wf
    #
    @3
    @5
    @2
    wceq
    cvv
    cvv
    c1st
    wfo
    @6
    fo1st
    cvv
    cvv
    c1st
    fof
    ax-mp
    cvv
    cvv
    cU
    c2nd
    c1st
    fvco3
    mpan
    syl5eq
    @3
    wn
    #
    @0
    c0
    @2
    cU
    cns
    fvprc
    @7
    @2
    c0
    c2nd
    cfv
    c0
    @7
    @1
    c0
    c2nd
    cU
    c1st
    fvprc
    fveq2d
    2nd0
    syl6req
    eqtrd
    pm2.61i
    eqtri
end
