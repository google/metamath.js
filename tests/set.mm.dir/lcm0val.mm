include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "clcm.mm"
include "co.mm"
include "wceq.mm"
include "0z.mm"
include "wa.mm"
include "wo.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "lcmval.mm"
include "eqid.mm"
include "olci.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "mpan2.mm"

theorem lcm0val
  let cM: class M
  let cK: class K
  let vn: setvar n
  let cN: class N


  assert |- ( M e. ZZ -> ( M lcm 0 ) = 0 )

  proof
    cM
    cz
    wcel
    #
    cc0
    cz
    wcel
    #
    cM
    cc0
    clcm
    co
    #
    cc0
    wceq
    0z
    @0
    @1
    wa
    @2
    cM
    cc0
    wceq
    #
    cc0
    cc0
    wceq
    #
    wo
    #
    cc0
    cM
    vn
    cv
    #
    cdvds
    wbr
    cc0
    @6
    cdvds
    wbr
    wa
    vn
    cn
    crab
    cr
    clt
    cinf
    #
    cif
    cc0
    vn
    cM
    cc0
    lcmval
    @5
    cc0
    @7
    @4
    @3
    cc0
    eqid
    olci
    iftruei
    syl6eq
    mpan2
end
