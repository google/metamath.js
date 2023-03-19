include "cc0.mm"
include "csqrt.mm"
include "cfv.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "w3a.mm"
include "cc.mm"
include "crio.mm"
include "wcel.mm"
include "0cn.mm"
include "sqrtval.mm"
include "ax-mp.mm"
include "id.mm"
include "wb.mm"
include "wa.mm"
include "sqr0lem.mm"
include "biimpi.mm"
include "ex.mm"
include "simpr.mm"
include "sylbir.mm"
include "impbid1.mm"
include "adantl.mm"
include "riota5.mm"
include "eqtri.mm"

theorem sqrt0
  let vx: setvar x


  assert |- ( sqrt ` 0 ) = 0

  proof
    cc0
    csqrt
    cfv
    #
    vx
    cv
    #
    c2
    cexp
    co
    cc0
    wceq
    cc0
    @1
    cre
    cfv
    cle
    wbr
    ci
    @1
    cmul
    co
    crp
    wnel
    w3a
    #
    vx
    cc
    crio
    #
    cc0
    cc0
    cc
    wcel
    #
    @0
    @3
    wceq
    0cn
    vx
    cc0
    sqrtval
    ax-mp
    @4
    @3
    cc0
    wceq
    0cn
    @4
    @2
    vx
    cc
    cc0
    @4
    id
    @1
    cc
    wcel
    #
    @2
    @1
    cc0
    wceq
    #
    wb
    @4
    @5
    @2
    @6
    @5
    @2
    @6
    @5
    @2
    wa
    #
    @6
    @1
    sqr0lem
    #
    biimpi
    ex
    @6
    @7
    @2
    @8
    @5
    @2
    simpr
    sylbir
    impbid1
    adantl
    riota5
    ax-mp
    eqtri
end
