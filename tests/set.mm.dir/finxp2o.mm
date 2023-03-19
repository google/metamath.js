include "c2o.mm"
include "cfinxp.mm"
include "c1o.mm"
include "csuc.mm"
include "cxp.mm"
include "wceq.mm"
include "df-2o.mm"
include "finxpeq2.mm"
include "ax-mp.mm"
include "com.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "1onn.mm"
include "1n0.mm"
include "finxpsuc.mm"
include "mp2an.mm"
include "finxp1o.mm"
include "xpeq1i.mm"
include "3eqtri.mm"

theorem finxp2o
  let cU: class U


  assert |- ( U ^^ 2o ) = ( U X. U )

  proof
    cU
    c2o
    cfinxp
    #
    cU
    c1o
    csuc
    #
    cfinxp
    #
    cU
    c1o
    cfinxp
    #
    cU
    cxp
    #
    cU
    cU
    cxp
    c2o
    @1
    wceq
    @0
    @2
    wceq
    df-2o
    cU
    c2o
    @1
    finxpeq2
    ax-mp
    c1o
    com
    wcel
    c1o
    c0
    wne
    @2
    @4
    wceq
    1onn
    1n0
    cU
    c1o
    finxpsuc
    mp2an
    @3
    cU
    cU
    cU
    finxp1o
    xpeq1i
    3eqtri
end
