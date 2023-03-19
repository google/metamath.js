include "cfmtno.mm"
include "cn0.mm"
include "wfn.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "ovex.mm"
include "df-fmtno.mm"
include "fnmpti.mm"
include "fvelrnb.mm"
include "ax-mp.mm"

theorem fmtnorn
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vx: setvar x

  disjoint F n
  disjoint k x
  assert |- ( F e. ran FermatNo <-> E. n e. NN0 ( FermatNo ` n ) = F )

  proof
    cfmtno
    cn0
    wfn
    cF
    cfmtno
    crn
    wcel
    vn
    cv
    #
    cfmtno
    cfv
    cF
    wceq
    vn
    cn0
    wrex
    wb
    vn
    cn0
    c2
    c2
    @0
    cexp
    co
    cexp
    co
    #
    c1
    caddc
    co
    cfmtno
    @1
    c1
    caddc
    ovex
    vn
    df-fmtno
    fnmpti
    vn
    cn0
    cF
    cfmtno
    fvelrnb
    ax-mp
end
