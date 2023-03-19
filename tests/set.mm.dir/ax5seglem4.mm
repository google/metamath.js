include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "wne.mm"
include "cc0.mm"
include "oveq2.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "biimpac.mm"
include "wb.mm"
include "eqeefv.mm"
include "3adant1.mm"
include "3adant3r3.mm"
include "eqcom.mm"
include "cc.mm"
include "simplr1.mm"
include "fveecn.mm"
include "sylancom.mm"
include "simplr3.mm"
include "mulid2.mm"
include "mul02.mm"
include "oveqan12d.mm"
include "addid1.mm"
include "adantr.mm"
include "eqtrd.mm"
include "syl2anc.mm"
include "eqeq1d.mm"
include "syl5rbbr.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "syl5ibr.mm"
include "expdimp.mm"
include "necon3d.mm"
include "3impia.mm"

theorem ax5seglem4
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let vi: setvar i
  let cN: class N

  disjoint A i
  disjoint B i
  disjoint C i
  disjoint N i
  disjoint T i
  assert |- ( ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) /\ A. i e. ( 1 ... N ) ( B ` i ) = ( ( ( 1 - T ) x. ( A ` i ) ) + ( T x. ( C ` i ) ) ) /\ A =/= B ) -> T =/= 0 )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    wa
    #
    vi
    cv
    #
    cB
    cfv
    #
    c1
    cT
    cmin
    co
    #
    @6
    cA
    cfv
    #
    cmul
    co
    #
    cT
    @6
    cC
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    cA
    cB
    wne
    cT
    cc0
    wne
    @5
    @16
    wa
    cT
    cc0
    cA
    cB
    @5
    @16
    cT
    cc0
    wceq
    #
    cA
    cB
    wceq
    #
    @16
    @17
    wa
    @18
    @5
    @7
    c1
    @9
    cmul
    co
    #
    cc0
    @11
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @15
    wral
    #
    @17
    @16
    @23
    @17
    @14
    @22
    vi
    @15
    @17
    @13
    @21
    @7
    @17
    @10
    @19
    @12
    @20
    caddc
    @17
    @8
    c1
    @9
    cmul
    @17
    @8
    c1
    cc0
    cmin
    co
    c1
    cT
    cc0
    c1
    cmin
    oveq2
    1m0e1
    syl6eq
    oveq1d
    cT
    cc0
    @11
    cmul
    oveq1
    oveq12d
    eqeq2d
    ralbidv
    biimpac
    @5
    @18
    @9
    @7
    wceq
    #
    vi
    @15
    wral
    #
    @23
    @0
    @2
    @3
    @18
    @25
    wb
    #
    @4
    @2
    @3
    @26
    @0
    cA
    cB
    vi
    cN
    eqeefv
    3adant1
    3adant3r3
    @5
    @24
    @22
    vi
    @15
    @22
    @21
    @7
    wceq
    @5
    @6
    @15
    wcel
    #
    wa
    #
    @24
    @21
    @7
    eqcom
    @28
    @21
    @9
    @7
    @28
    @9
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    @21
    @9
    wceq
    @5
    @27
    @2
    @29
    @2
    @3
    @4
    @0
    @27
    simplr1
    cA
    @6
    cN
    fveecn
    sylancom
    @5
    @27
    @4
    @30
    @2
    @3
    @4
    @0
    @27
    simplr3
    cC
    @6
    cN
    fveecn
    sylancom
    @29
    @30
    wa
    @21
    @9
    cc0
    caddc
    co
    #
    @9
    @29
    @30
    @19
    @9
    @20
    cc0
    caddc
    @9
    mulid2
    @11
    mul02
    oveqan12d
    @29
    @31
    @9
    wceq
    @30
    @9
    addid1
    adantr
    eqtrd
    syl2anc
    eqeq1d
    syl5rbbr
    ralbidva
    bitrd
    syl5ibr
    expdimp
    necon3d
    3impia
end
