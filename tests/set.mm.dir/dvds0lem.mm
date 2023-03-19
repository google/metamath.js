include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "adantl.mm"
include "wb.mm"
include "divides.mm"
include "adantr.mm"
include "mpbird.mm"
include "expr.mm"
include "3impa.mm"
include "3comr.mm"
include "imp.mm"

theorem dvds0lem
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) /\ ( K x. M ) = N ) -> M || N )

  proof
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    cK
    cM
    cmul
    co
    #
    cN
    wceq
    #
    cM
    cN
    cdvds
    wbr
    #
    @1
    @2
    @0
    @4
    @5
    wi
    #
    @1
    @2
    @0
    @6
    @1
    @2
    wa
    #
    @0
    @4
    @5
    @7
    @0
    @4
    wa
    #
    wa
    @5
    vx
    cv
    #
    cM
    cmul
    co
    #
    cN
    wceq
    #
    vx
    cz
    wrex
    #
    @8
    @12
    @7
    @11
    @4
    vx
    cK
    cz
    @9
    cK
    wceq
    @10
    @3
    cN
    @9
    cK
    cM
    cmul
    oveq1
    eqeq1d
    rspcev
    adantl
    @7
    @5
    @12
    wb
    @8
    vx
    cM
    cN
    divides
    adantr
    mpbird
    expr
    3impa
    3comr
    imp
end
