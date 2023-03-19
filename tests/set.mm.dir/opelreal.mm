include "c0r.mm"
include "cop.mm"
include "cr.mm"
include "wcel.mm"
include "cnr.mm"
include "wceq.mm"
include "eqid.mm"
include "csn.mm"
include "cxp.mm"
include "wa.mm"
include "df-r.mm"
include "eleq2i.mm"
include "opelxp.mm"
include "0r.mm"
include "elexi.mm"
include "elsn.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "mpbiran2.mm"

theorem opelreal
  let cA: class A


  assert |- ( <. A , 0R >. e. RR <-> A e. R. )

  proof
    cA
    c0r
    cop
    #
    cr
    wcel
    #
    cA
    cnr
    wcel
    #
    c0r
    c0r
    wceq
    #
    c0r
    eqid
    @1
    @0
    cnr
    c0r
    csn
    #
    cxp
    #
    wcel
    @2
    c0r
    @4
    wcel
    #
    wa
    @2
    @3
    wa
    cr
    @5
    @0
    df-r
    eleq2i
    cA
    c0r
    cnr
    @4
    opelxp
    @6
    @3
    @2
    c0r
    c0r
    c0r
    cnr
    0r
    elexi
    elsn
    anbi2i
    3bitri
    mpbiran2
end
