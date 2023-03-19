include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "cn0.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "cgcd.mm"
include "wf.mm"
include "co.mm"
include "gcdval.mm"
include "gcdcl.mm"
include "eqeltrrd.mm"
include "rgen2a.mm"
include "df-gcd.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem gcdf
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- gcd : ( ZZ X. ZZ ) --> NN0

  proof
    vx
    cv
    #
    cc0
    wceq
    vy
    cv
    #
    cc0
    wceq
    wa
    cc0
    vn
    cv
    #
    @0
    cdvds
    wbr
    @2
    @1
    cdvds
    wbr
    wa
    vn
    cz
    crab
    cr
    clt
    csup
    cif
    #
    cn0
    wcel
    #
    vy
    cz
    wral
    vx
    cz
    wral
    cz
    cz
    cxp
    cn0
    cgcd
    wf
    @4
    vx
    vy
    cz
    @0
    cz
    wcel
    @1
    cz
    wcel
    wa
    @0
    @1
    cgcd
    co
    @3
    cn0
    vn
    @0
    @1
    gcdval
    @0
    @1
    gcdcl
    eqeltrrd
    rgen2a
    vx
    vy
    cz
    cz
    @3
    cn0
    cgcd
    vx
    vy
    vn
    df-gcd
    fmpt2
    mpbi
end
