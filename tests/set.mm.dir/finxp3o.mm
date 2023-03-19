include "c3o.mm"
include "cfinxp.mm"
include "c2o.mm"
include "csuc.mm"
include "cxp.mm"
include "wceq.mm"
include "df-3o.mm"
include "finxpeq2.mm"
include "ax-mp.mm"
include "com.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "2onn.mm"
include "2on0.mm"
include "finxpsuc.mm"
include "mp2an.mm"
include "finxp2o.mm"
include "xpeq1i.mm"
include "3eqtri.mm"

theorem finxp3o
  let cU: class U


  assert |- ( U ^^ 3o ) = ( ( U X. U ) X. U )

  proof
    cU
    c3o
    cfinxp
    #
    cU
    c2o
    csuc
    #
    cfinxp
    #
    cU
    c2o
    cfinxp
    #
    cU
    cxp
    #
    cU
    cU
    cxp
    #
    cU
    cxp
    c3o
    @1
    wceq
    @0
    @2
    wceq
    df-3o
    cU
    c3o
    @1
    finxpeq2
    ax-mp
    c2o
    com
    wcel
    c2o
    c0
    wne
    @2
    @4
    wceq
    2onn
    2on0
    cU
    c2o
    finxpsuc
    mp2an
    @3
    @5
    cU
    cU
    finxp2o
    xpeq1i
    3eqtri
end
