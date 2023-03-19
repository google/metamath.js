include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "ch0o.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "cmv.mm"
include "cmin.mm"
include "ci.mm"
include "csm.mm"
include "cmul.mm"
include "caddc.mm"
include "c4.mm"
include "cdiv.mm"
include "lnopeq0lem2.mm"
include "adantl.mm"
include "hvaddcl.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "rspccva.mm"
include "sylan2.mm"
include "hvsubcl.mm"
include "0m0e0.mm"
include "syl6eq.mm"
include "cc.mm"
include "ax-icn.mm"
include "hvmulcl.mm"
include "mpan.mm"
include "oveq2d.mm"
include "it0e0.mm"
include "00id.mm"
include "oveq1d.mm"
include "4cn.mm"
include "4ne0.mm"
include "div0i.mm"
include "eqtrd.mm"
include "ralrimivva.mm"
include "lnopfi.mm"
include "ho01i.mm"
include "sylib.mm"
include "c0v.mm"
include "fveq1.mm"
include "ho0val.mm"
include "sylan9eq.mm"
include "hi01.mm"
include "ralrimiva.mm"
include "impbii.mm"

theorem lnopeq0i
  let vx: setvar x
  let cT: class T
  let vy: setvar y
  let vz: setvar z
  assume lnopeq0.1: |- T e. LinOp

  disjoint T x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint T y
  disjoint T z
  assert |- ( A. x e. ~H ( ( T ` x ) .ih x ) = 0 <-> T = 0hop )

  proof
    vx
    cv
    #
    cT
    cfv
    #
    @0
    csp
    co
    #
    cc0
    wceq
    #
    vx
    chil
    wral
    #
    cT
    ch0o
    wceq
    #
    @4
    vy
    cv
    #
    cT
    cfv
    vz
    cv
    #
    csp
    co
    #
    cc0
    wceq
    #
    vz
    chil
    wral
    vy
    chil
    wral
    @5
    @4
    @9
    vy
    vz
    chil
    chil
    @4
    @6
    chil
    wcel
    #
    @7
    chil
    wcel
    #
    wa
    #
    wa
    #
    @8
    @6
    @7
    cva
    co
    #
    cT
    cfv
    #
    @14
    csp
    co
    #
    @6
    @7
    cmv
    co
    #
    cT
    cfv
    #
    @17
    csp
    co
    #
    cmin
    co
    #
    ci
    @6
    ci
    @7
    csm
    co
    #
    cva
    co
    #
    cT
    cfv
    #
    @22
    csp
    co
    #
    @6
    @21
    cmv
    co
    #
    cT
    cfv
    #
    @25
    csp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    #
    cc0
    @12
    @8
    @31
    wceq
    @4
    @6
    @7
    cT
    lnopeq0.1
    lnopeq0lem2
    adantl
    @13
    @31
    cc0
    c4
    cdiv
    co
    cc0
    @13
    @30
    cc0
    c4
    cdiv
    @13
    @30
    cc0
    cc0
    caddc
    co
    cc0
    @13
    @20
    cc0
    @29
    cc0
    caddc
    @13
    @20
    cc0
    cc0
    cmin
    co
    #
    cc0
    @13
    @16
    cc0
    @19
    cc0
    cmin
    @12
    @4
    @14
    chil
    wcel
    @16
    cc0
    wceq
    #
    @6
    @7
    hvaddcl
    @3
    @33
    vx
    @14
    chil
    @0
    @14
    wceq
    #
    @2
    @16
    cc0
    @34
    @1
    @15
    @0
    @14
    csp
    @0
    @14
    cT
    fveq2
    @34
    id
    oveq12d
    eqeq1d
    rspccva
    sylan2
    @12
    @4
    @17
    chil
    wcel
    @19
    cc0
    wceq
    #
    @6
    @7
    hvsubcl
    @3
    @35
    vx
    @17
    chil
    @0
    @17
    wceq
    #
    @2
    @19
    cc0
    @36
    @1
    @18
    @0
    @17
    csp
    @0
    @17
    cT
    fveq2
    @36
    id
    oveq12d
    eqeq1d
    rspccva
    sylan2
    oveq12d
    0m0e0
    syl6eq
    @13
    @29
    ci
    cc0
    cmul
    co
    cc0
    @13
    @28
    cc0
    ci
    cmul
    @13
    @28
    @32
    cc0
    @13
    @24
    cc0
    @27
    cc0
    cmin
    @12
    @4
    @22
    chil
    wcel
    #
    @24
    cc0
    wceq
    #
    @11
    @10
    @21
    chil
    wcel
    #
    @37
    ci
    cc
    wcel
    @11
    @39
    ax-icn
    ci
    @7
    hvmulcl
    mpan
    #
    @6
    @21
    hvaddcl
    sylan2
    @3
    @38
    vx
    @22
    chil
    @0
    @22
    wceq
    #
    @2
    @24
    cc0
    @41
    @1
    @23
    @0
    @22
    csp
    @0
    @22
    cT
    fveq2
    @41
    id
    oveq12d
    eqeq1d
    rspccva
    sylan2
    @12
    @4
    @25
    chil
    wcel
    #
    @27
    cc0
    wceq
    #
    @11
    @10
    @39
    @42
    @40
    @6
    @21
    hvsubcl
    sylan2
    @3
    @43
    vx
    @25
    chil
    @0
    @25
    wceq
    #
    @2
    @27
    cc0
    @44
    @1
    @26
    @0
    @25
    csp
    @0
    @25
    cT
    fveq2
    @44
    id
    oveq12d
    eqeq1d
    rspccva
    sylan2
    oveq12d
    0m0e0
    syl6eq
    oveq2d
    it0e0
    syl6eq
    oveq12d
    00id
    syl6eq
    oveq1d
    c4
    4cn
    4ne0
    div0i
    syl6eq
    eqtrd
    ralrimivva
    vy
    vz
    cT
    cT
    lnopeq0.1
    lnopfi
    ho01i
    sylib
    @5
    @3
    vx
    chil
    @5
    @0
    chil
    wcel
    #
    wa
    #
    @2
    c0v
    @0
    csp
    co
    #
    cc0
    @46
    @1
    c0v
    @0
    csp
    @5
    @45
    @1
    @0
    ch0o
    cfv
    c0v
    @0
    cT
    ch0o
    fveq1
    @0
    ho0val
    sylan9eq
    oveq1d
    @45
    @47
    cc0
    wceq
    @5
    @0
    hi01
    adantl
    eqtrd
    ralrimiva
    impbii
end
