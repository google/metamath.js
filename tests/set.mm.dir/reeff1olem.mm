include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "cioo.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "ce.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cicc.mm"
include "ioossicc.mm"
include "0re.mm"
include "iccssre.mm"
include "mpan.mm"
include "adantr.mm"
include "syl5ss.mm"
include "cc.mm"
include "a1i.mm"
include "simpl.mm"
include "0lt1.mm"
include "wi.mm"
include "1re.mm"
include "lttr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "imp.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "ccncf.mm"
include "efcn.mm"
include "ssel2.mm"
include "reefcld.mm"
include "sylan.mm"
include "ef0.mm"
include "simpr.mm"
include "syl5eqbr.mm"
include "caddc.mm"
include "peano2re.mm"
include "reefcl.mm"
include "ltp1.mm"
include "recnd.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "sylancl.mm"
include "crp.mm"
include "elrpd.mm"
include "efgt1p.mm"
include "syl.mm"
include "eqbrtrd.mm"
include "lttrd.mm"
include "jca.mm"
include "ivth.mm"
include "ssrexv.mm"
include "sylc.mm"

theorem reeff1olem
  let vx: setvar x
  let cU: class U
  let vy: setvar y

  disjoint U x
  disjoint U y
  disjoint x y
  assert |- ( ( U e. RR /\ 1 < U ) -> E. x e. RR ( exp ` x ) = U )

  proof
    cU
    cr
    wcel
    #
    c1
    cU
    clt
    wbr
    #
    wa
    #
    cc0
    cU
    cioo
    co
    #
    cr
    wss
    vx
    cv
    ce
    cfv
    cU
    wceq
    #
    vx
    @3
    wrex
    @4
    vx
    cr
    wrex
    @2
    @3
    cc0
    cU
    cicc
    co
    #
    cr
    cc0
    cU
    ioossicc
    @0
    @5
    cr
    wss
    #
    @1
    cc0
    cr
    wcel
    #
    @0
    @6
    0re
    cc0
    cU
    iccssre
    mpan
    adantr
    #
    syl5ss
    @2
    vy
    cc0
    cU
    cc
    cU
    ce
    vx
    @7
    @2
    0re
    a1i
    @0
    @1
    simpl
    #
    @9
    @0
    @1
    cc0
    cU
    clt
    wbr
    #
    @0
    cc0
    c1
    clt
    wbr
    #
    @1
    @10
    0lt1
    @7
    c1
    cr
    wcel
    @0
    @11
    @1
    wa
    @10
    wi
    0re
    1re
    cc0
    c1
    cU
    lttr
    mp3an12
    mpani
    imp
    #
    @2
    @5
    cr
    cc
    @8
    ax-resscn
    syl6ss
    ce
    cc
    cc
    ccncf
    co
    wcel
    @2
    efcn
    a1i
    @2
    @6
    vy
    cv
    #
    @5
    wcel
    #
    @13
    ce
    cfv
    cr
    wcel
    @8
    @6
    @14
    wa
    @13
    @5
    cr
    @13
    ssel2
    reefcld
    sylan
    @2
    cc0
    ce
    cfv
    #
    cU
    clt
    wbr
    cU
    cU
    ce
    cfv
    #
    clt
    wbr
    @2
    @15
    c1
    cU
    clt
    ef0
    @0
    @1
    simpr
    syl5eqbr
    @2
    cU
    cU
    c1
    caddc
    co
    #
    @16
    @9
    @0
    @17
    cr
    wcel
    @1
    cU
    peano2re
    adantr
    @0
    @16
    cr
    wcel
    @1
    cU
    reefcl
    adantr
    @0
    cU
    @17
    clt
    wbr
    @1
    cU
    ltp1
    adantr
    @2
    @17
    c1
    cU
    caddc
    co
    #
    @16
    clt
    @2
    cU
    cc
    wcel
    c1
    cc
    wcel
    @17
    @18
    wceq
    @2
    cU
    @9
    recnd
    ax-1cn
    cU
    c1
    addcom
    sylancl
    @2
    cU
    crp
    wcel
    @18
    @16
    clt
    wbr
    @2
    cU
    @9
    @12
    elrpd
    cU
    efgt1p
    syl
    eqbrtrd
    lttrd
    jca
    ivth
    @4
    vx
    @3
    cr
    ssrexv
    sylc
end
