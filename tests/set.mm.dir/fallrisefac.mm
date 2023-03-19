include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cfallfac.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "cmul.mm"
include "crisefac.mm"
include "wceq.mm"
include "c2.mm"
include "caddc.mm"
include "nn0cn.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "cz.mm"
include "nn0z.mm"
include "m1expeven.mm"
include "syl.mm"
include "neg1cn.mm"
include "expadd.mm"
include "mp3an1.mm"
include "anidms.mm"
include "3eqtr3rd.mm"
include "adantl.mm"
include "negneg.mm"
include "adantr.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "expcl.mm"
include "mpan.mm"
include "negcl.mm"
include "negcld.mm"
include "fallfaccl.mm"
include "sylan.mm"
include "mulassd.mm"
include "mulid2d.mm"
include "risefallfac.mm"
include "eqtr4d.mm"

theorem fallrisefac
  let cN: class N
  let cX: class X


  assert |- ( ( X e. CC /\ N e. NN0 ) -> ( X FallFac N ) = ( ( -u 1 ^ N ) x. ( -u X RiseFac N ) ) )

  proof
    cX
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cX
    cN
    cfallfac
    co
    #
    c1
    cneg
    #
    cN
    cexp
    co
    #
    @5
    cX
    cneg
    #
    cneg
    #
    cN
    cfallfac
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @5
    @6
    cN
    crisefac
    co
    #
    cmul
    co
    @2
    @5
    @5
    cmul
    co
    #
    @8
    cmul
    co
    c1
    @3
    cmul
    co
    @10
    @3
    @2
    @12
    c1
    @8
    @3
    cmul
    @1
    @12
    c1
    wceq
    @0
    @1
    @4
    c2
    cN
    cmul
    co
    #
    cexp
    co
    #
    @4
    cN
    cN
    caddc
    co
    #
    cexp
    co
    #
    c1
    @12
    @1
    @13
    @15
    @4
    cexp
    @1
    cN
    cN
    nn0cn
    2timesd
    oveq2d
    @1
    cN
    cz
    wcel
    @14
    c1
    wceq
    cN
    nn0z
    cN
    m1expeven
    syl
    @1
    @16
    @12
    wceq
    #
    @4
    cc
    wcel
    #
    @1
    @1
    @17
    neg1cn
    @4
    cN
    cN
    expadd
    mp3an1
    anidms
    3eqtr3rd
    adantl
    @2
    @7
    cX
    cN
    cfallfac
    @0
    @7
    cX
    wceq
    @1
    cX
    negneg
    adantr
    oveq1d
    oveq12d
    @2
    @5
    @5
    @8
    @1
    @5
    cc
    wcel
    #
    @0
    @18
    @1
    @19
    neg1cn
    @4
    cN
    expcl
    mpan
    adantl
    #
    @20
    @0
    @7
    cc
    wcel
    @1
    @8
    cc
    wcel
    @0
    @6
    cX
    negcl
    #
    negcld
    @7
    cN
    fallfaccl
    sylan
    mulassd
    @2
    @3
    cX
    cN
    fallfaccl
    mulid2d
    3eqtr3rd
    @2
    @11
    @9
    @5
    cmul
    @0
    @6
    cc
    wcel
    @1
    @11
    @9
    wceq
    @21
    cN
    @6
    risefallfac
    sylan
    oveq2d
    eqtr4d
end
