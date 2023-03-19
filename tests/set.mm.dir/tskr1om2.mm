include "ctsk.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cr1.mm"
include "com.mm"
include "cima.mm"
include "cuni.mm"
include "cv.mm"
include "wrex.mm"
include "eluni2.mm"
include "wss.mm"
include "wi.mm"
include "cfv.mm"
include "wceq.mm"
include "wtr.mm"
include "wfun.mm"
include "con0.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "fvelima.mm"
include "mpan.mm"
include "r1tr.mm"
include "treq.mm"
include "mpbii.mm"
include "rexlimivw.mm"
include "trss.mm"
include "3syl.mm"
include "adantl.mm"
include "tskr1om.mm"
include "sseld.mm"
include "tskss.mm"
include "3exp.mm"
include "adantr.mm"
include "syld.mm"
include "imp.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem tskr1om2
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( T e. Tarski /\ T =/= (/) ) -> U. ( R1 " _om ) C_ T )

  proof
    cT
    ctsk
    wcel
    #
    cT
    c0
    wne
    #
    wa
    #
    vy
    cr1
    com
    cima
    #
    cuni
    #
    cT
    vy
    cv
    #
    @4
    wcel
    @5
    vx
    cv
    #
    wcel
    #
    vx
    @3
    wrex
    @2
    @5
    cT
    wcel
    #
    vx
    @5
    @3
    eluni2
    @2
    @7
    @8
    vx
    @3
    @2
    @6
    @3
    wcel
    #
    wa
    @7
    @5
    @6
    wss
    #
    @8
    @9
    @7
    @10
    wi
    #
    @2
    @9
    @5
    cr1
    cfv
    #
    @6
    wceq
    #
    vy
    com
    wrex
    #
    @6
    wtr
    #
    @11
    cr1
    wfun
    #
    @9
    @14
    cr1
    con0
    wfn
    @16
    r1fnon
    con0
    cr1
    fnfun
    ax-mp
    vy
    @6
    com
    cr1
    fvelima
    mpan
    @13
    @15
    vy
    com
    @13
    @12
    wtr
    @15
    @5
    r1tr
    @12
    @6
    treq
    mpbii
    rexlimivw
    @6
    @5
    trss
    3syl
    adantl
    @2
    @9
    @10
    @8
    wi
    #
    @2
    @9
    @6
    cT
    wcel
    #
    @17
    @2
    @3
    cT
    @6
    cT
    tskr1om
    sseld
    @0
    @18
    @17
    wi
    @1
    @0
    @18
    @10
    @8
    @6
    @5
    cT
    tskss
    3exp
    adantr
    syld
    imp
    syld
    rexlimdva
    syl5bi
    ssrdv
end
