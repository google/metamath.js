include "c3.mm"
include "c5.mm"
include "c7.mm"
include "ctp.mm"
include "wceq.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cpr.mm"
include "pweq.mm"
include "qdass.mm"
include "qdassr.mm"
include "uneq12i.mm"
include "pwtp.mm"
include "df-tp.mm"
include "uneq2i.mm"
include "unass.mm"
include "eqtr4i.mm"
include "tpass.mm"
include "uneq1i.mm"
include "3eqtr4i.mm"
include "un4.mm"
include "syl6eq.mm"

theorem ex-pw
  let cA: class A


  assert |- ( A = { 3 , 5 , 7 } -> ~P A = ( ( { (/) } u. { { 3 } , { 5 } , { 7 } } ) u. ( { { 3 , 5 } , { 3 , 7 } , { 5 , 7 } } u. { { 3 , 5 , 7 } } ) ) )

  proof
    cA
    c3
    c5
    c7
    ctp
    #
    wceq
    cA
    cpw
    @0
    cpw
    #
    c0
    csn
    #
    c3
    csn
    #
    c5
    csn
    #
    c7
    csn
    #
    ctp
    #
    cun
    #
    c3
    c5
    cpr
    #
    c3
    c7
    cpr
    #
    c5
    c7
    cpr
    #
    ctp
    #
    @0
    csn
    #
    cun
    #
    cun
    #
    cA
    @0
    pweq
    c0
    @3
    cpr
    @4
    @8
    cpr
    cun
    #
    @5
    @9
    cpr
    @10
    @0
    cpr
    cun
    #
    cun
    c0
    @3
    @4
    ctp
    #
    @8
    csn
    #
    cun
    #
    @5
    csn
    #
    @9
    @10
    @0
    ctp
    #
    cun
    #
    cun
    #
    @1
    @14
    @15
    @19
    @16
    @22
    c0
    @3
    @4
    @8
    qdass
    @5
    @9
    @10
    @0
    qdassr
    uneq12i
    c3
    c5
    c7
    pwtp
    @14
    @17
    @20
    cun
    #
    @18
    @21
    cun
    #
    cun
    @23
    @7
    @24
    @13
    @25
    @7
    @2
    @3
    @4
    cpr
    #
    cun
    #
    @20
    cun
    #
    @24
    @7
    @2
    @26
    @20
    cun
    #
    cun
    @28
    @6
    @29
    @2
    @3
    @4
    @5
    df-tp
    uneq2i
    @2
    @26
    @20
    unass
    eqtr4i
    @17
    @27
    @20
    c0
    @3
    @4
    tpass
    uneq1i
    eqtr4i
    @18
    @9
    @10
    cpr
    #
    cun
    #
    @12
    cun
    @18
    @30
    @12
    cun
    #
    cun
    @13
    @25
    @18
    @30
    @12
    unass
    @11
    @31
    @12
    @8
    @9
    @10
    tpass
    uneq1i
    @21
    @32
    @18
    @9
    @10
    @0
    df-tp
    uneq2i
    3eqtr4i
    uneq12i
    @17
    @18
    @20
    @21
    un4
    eqtr4i
    3eqtr4i
    syl6eq
end
