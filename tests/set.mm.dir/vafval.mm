include "cpv.mm"
include "cfv.mm"
include "c1st.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ccom.mm"
include "df-va.mm"
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
include "1st0.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem vafval
  let cU: class U
  let cG: class G
  assume vafval.2: |- G = ( +v ` U )


  assert |- G = ( 1st ` ( 1st ` U ) )

  proof
    cG
    cU
    cpv
    cfv
    #
    cU
    c1st
    cfv
    #
    c1st
    cfv
    #
    vafval.2
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
    c1st
    c1st
    ccom
    #
    cfv
    #
    @2
    cU
    cpv
    @4
    df-va
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
    c1st
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
    cpv
    fvprc
    @7
    @2
    c0
    c1st
    cfv
    c0
    @7
    @1
    c0
    c1st
    cU
    c1st
    fvprc
    fveq2d
    1st0
    syl6req
    eqtrd
    pm2.61i
    eqtri
end
