include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "cmul.mm"
include "csin.mm"
include "cmin.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "negcl.mm"
include "cosadd.mm"
include "mpdan.mm"
include "cc0.mm"
include "negid.mm"
include "fveq2d.mm"
include "cos0.mm"
include "syl6eq.mm"
include "sincl.mm"
include "sqcld.mm"
include "coscl.mm"
include "addcomd.mm"
include "sqvald.mm"
include "cosneg.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "sinneg.mm"
include "negeqd.mm"
include "negnegd.mm"
include "eqtrd.mm"
include "sincld.mm"
include "mulneg2d.mm"
include "oveq12d.mm"
include "coscld.mm"
include "mulcld.mm"
include "negsubd.mm"
include "3eqtrrd.mm"
include "3eqtr3rd.mm"

theorem sincossq
  let cA: class A


  assert |- ( A e. CC -> ( ( ( sin ` A ) ^ 2 ) + ( ( cos ` A ) ^ 2 ) ) = 1 )

  proof
    cA
    cc
    wcel
    #
    cA
    cA
    cneg
    #
    caddc
    co
    #
    ccos
    cfv
    #
    cA
    ccos
    cfv
    #
    @1
    ccos
    cfv
    #
    cmul
    co
    #
    cA
    csin
    cfv
    #
    @1
    csin
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    c1
    @7
    c2
    cexp
    co
    #
    @4
    c2
    cexp
    co
    #
    caddc
    co
    #
    @0
    @1
    cc
    wcel
    @3
    @10
    wceq
    cA
    negcl
    #
    cA
    @1
    cosadd
    mpdan
    @0
    @3
    cc0
    ccos
    cfv
    c1
    @0
    @2
    cc0
    ccos
    cA
    negid
    fveq2d
    cos0
    syl6eq
    @0
    @13
    @12
    @11
    caddc
    co
    @6
    @9
    cneg
    #
    caddc
    co
    @10
    @0
    @11
    @12
    @0
    @7
    cA
    sincl
    #
    sqcld
    @0
    @4
    cA
    coscl
    #
    sqcld
    addcomd
    @0
    @12
    @6
    @11
    @15
    caddc
    @0
    @12
    @4
    @4
    cmul
    co
    @6
    @0
    @4
    @17
    sqvald
    @0
    @5
    @4
    @4
    cmul
    cA
    cosneg
    oveq2d
    eqtr4d
    @0
    @11
    @7
    @8
    cneg
    #
    cmul
    co
    #
    @15
    @0
    @11
    @7
    @7
    cmul
    co
    @19
    @0
    @7
    @16
    sqvald
    @0
    @18
    @7
    @7
    cmul
    @0
    @18
    @7
    cneg
    #
    cneg
    @7
    @0
    @8
    @20
    cA
    sinneg
    negeqd
    @0
    @7
    @16
    negnegd
    eqtrd
    oveq2d
    eqtr4d
    @0
    @7
    @8
    @16
    @0
    @1
    @14
    sincld
    #
    mulneg2d
    eqtrd
    oveq12d
    @0
    @6
    @9
    @0
    @4
    @5
    @17
    @0
    @1
    @14
    coscld
    mulcld
    @0
    @7
    @8
    @16
    @21
    mulcld
    negsubd
    3eqtrrd
    3eqtr3rd
end
