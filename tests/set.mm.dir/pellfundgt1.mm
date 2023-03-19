include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cpellfund.mm"
include "1red.mm"
include "eldifi.mm"
include "peano2nnd.mm"
include "nnrpd.mm"
include "rpsqrtcld.mm"
include "rpred.mm"
include "readdcld.mm"
include "pellfundre.mm"
include "cr.mm"
include "sqrt1.mm"
include "syl5eqel.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "1lt2.mm"
include "oveq12i.mm"
include "1p1e2.mm"
include "eqtri.mm"
include "breqtrri.mm"
include "a1i.mm"
include "cle.mm"
include "nnge1d.mm"
include "cc0.mm"
include "0le1.mm"
include "nnred.mm"
include "peano2re.mm"
include "syl.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "sqrtled.mm"
include "mpbid.mm"
include "le2addd.mm"
include "ltletrd.mm"
include "pellfundge.mm"

theorem pellfundgt1
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  let vx: setvar x


  assert |- ( D e. ( NN \ []NN ) -> 1 < ( PellFund ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    c1
    cD
    c1
    caddc
    co
    #
    csqrt
    cfv
    #
    cD
    csqrt
    cfv
    #
    caddc
    co
    #
    cD
    cpellfund
    cfv
    @0
    1red
    #
    @0
    @2
    @3
    @0
    @2
    @0
    @1
    @0
    @1
    @0
    cD
    cD
    cn
    csquarenn
    eldifi
    #
    peano2nnd
    #
    nnrpd
    rpsqrtcld
    rpred
    #
    @0
    @3
    @0
    cD
    @0
    cD
    @6
    nnrpd
    rpsqrtcld
    rpred
    #
    readdcld
    #
    cD
    pellfundre
    @0
    c1
    c1
    csqrt
    cfv
    #
    @11
    caddc
    co
    #
    @4
    @5
    @0
    @11
    @11
    @0
    @11
    c1
    cr
    sqrt1
    @5
    syl5eqel
    #
    @13
    readdcld
    @10
    c1
    @12
    clt
    wbr
    @0
    c1
    c2
    @12
    clt
    1lt2
    @12
    c1
    c1
    caddc
    co
    c2
    @11
    c1
    @11
    c1
    caddc
    sqrt1
    sqrt1
    oveq12i
    1p1e2
    eqtri
    breqtrri
    a1i
    @0
    @11
    @11
    @2
    @3
    @13
    @13
    @8
    @9
    @0
    c1
    @1
    cle
    wbr
    @11
    @2
    cle
    wbr
    @0
    @1
    @7
    nnge1d
    @0
    c1
    @1
    @5
    cc0
    c1
    cle
    wbr
    @0
    0le1
    a1i
    #
    @0
    cD
    cr
    wcel
    @1
    cr
    wcel
    @0
    cD
    @6
    nnred
    #
    cD
    peano2re
    syl
    @0
    @1
    @0
    @1
    @7
    nnnn0d
    nn0ge0d
    sqrtled
    mpbid
    @0
    c1
    cD
    cle
    wbr
    @11
    @3
    cle
    wbr
    @0
    cD
    @6
    nnge1d
    @0
    c1
    cD
    @5
    @14
    @15
    @0
    cD
    @0
    cD
    @6
    nnnn0d
    nn0ge0d
    sqrtled
    mpbid
    le2addd
    ltletrd
    cD
    pellfundge
    ltletrd
end
