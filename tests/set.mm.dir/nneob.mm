include "com.mm"
include "wcel.mm"
include "c2o.mm"
include "cv.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "csuc.mm"
include "wn.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "wa.mm"
include "nnneo.mm"
include "3com23.mm"
include "3expa.mm"
include "nrexdv.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "wi.mm"
include "c0.mm"
include "suceq.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "notbid.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "peano1.mm"
include "eqid.mm"
include "om0x.mm"
include "syl6eq.mm"
include "rspcev.mm"
include "mp2an.mm"
include "a1i.mm"
include "peano2.mm"
include "coa.mm"
include "c1o.mm"
include "2onn.mm"
include "nnmsuc.mm"
include "mpan.mm"
include "df-2o.mm"
include "oveq2i.mm"
include "nnmcl.mm"
include "1onn.mm"
include "nnasuc.mm"
include "sylancl.mm"
include "syl5req.mm"
include "con0.mm"
include "nnon.mm"
include "oa1suc.mm"
include "4syl.mm"
include "3eqtr2rd.mm"
include "syl2anc.mm"
include "syl.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "syl5bi.mm"
include "con3d.mm"
include "con1.mm"
include "syl9.mm"
include "finds.mm"
include "impbid2.mm"

theorem nneob
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A e. _om -> ( E. x e. _om A = ( 2o .o x ) <-> -. E. x e. _om suc A = ( 2o .o x ) ) )

  proof
    cA
    com
    wcel
    cA
    c2o
    vx
    cv
    #
    comu
    co
    #
    wceq
    #
    vx
    com
    wrex
    #
    cA
    csuc
    #
    @1
    wceq
    #
    vx
    com
    wrex
    #
    wn
    #
    @3
    cA
    c2o
    vy
    cv
    #
    comu
    co
    #
    wceq
    #
    vy
    com
    wrex
    @7
    @2
    @10
    vx
    vy
    com
    @0
    @8
    wceq
    #
    @1
    @9
    cA
    @0
    @8
    c2o
    comu
    oveq2
    #
    eqeq2d
    cbvrexv
    @10
    @7
    vy
    com
    @8
    com
    wcel
    #
    @10
    wa
    @5
    vx
    com
    @13
    @10
    @0
    com
    wcel
    #
    @5
    wn
    #
    @13
    @14
    @10
    @15
    @8
    @0
    cA
    nnneo
    3com23
    3expa
    nrexdv
    rexlimiva
    sylbi
    @8
    csuc
    #
    @1
    wceq
    #
    vx
    com
    wrex
    #
    wn
    #
    @8
    @1
    wceq
    #
    vx
    com
    wrex
    #
    wi
    c0
    csuc
    #
    @1
    wceq
    #
    vx
    com
    wrex
    #
    wn
    #
    c0
    @1
    wceq
    #
    vx
    com
    wrex
    #
    wi
    vz
    cv
    #
    csuc
    #
    @1
    wceq
    #
    vx
    com
    wrex
    #
    wn
    #
    @28
    @1
    wceq
    #
    vx
    com
    wrex
    #
    wi
    #
    @29
    csuc
    #
    @1
    wceq
    #
    vx
    com
    wrex
    #
    wn
    #
    @31
    wi
    @7
    @3
    wi
    vy
    vz
    cA
    @8
    c0
    wceq
    #
    @19
    @25
    @21
    @27
    @40
    @18
    @24
    @40
    @17
    @23
    vx
    com
    @40
    @16
    @22
    @1
    @8
    c0
    suceq
    eqeq1d
    rexbidv
    notbid
    @40
    @20
    @26
    vx
    com
    @8
    c0
    @1
    eqeq1
    rexbidv
    imbi12d
    @8
    @28
    wceq
    #
    @19
    @32
    @21
    @34
    @41
    @18
    @31
    @41
    @17
    @30
    vx
    com
    @41
    @16
    @29
    @1
    @8
    @28
    suceq
    eqeq1d
    rexbidv
    notbid
    @41
    @20
    @33
    vx
    com
    @8
    @28
    @1
    eqeq1
    rexbidv
    imbi12d
    @8
    @29
    wceq
    #
    @19
    @39
    @21
    @31
    @42
    @18
    @38
    @42
    @17
    @37
    vx
    com
    @42
    @16
    @36
    @1
    @8
    @29
    suceq
    eqeq1d
    rexbidv
    notbid
    @42
    @20
    @30
    vx
    com
    @8
    @29
    @1
    eqeq1
    rexbidv
    imbi12d
    @8
    cA
    wceq
    #
    @19
    @7
    @21
    @3
    @43
    @18
    @6
    @43
    @17
    @5
    vx
    com
    @43
    @16
    @4
    @1
    @8
    cA
    suceq
    eqeq1d
    rexbidv
    notbid
    @43
    @20
    @2
    vx
    com
    @8
    cA
    @1
    eqeq1
    rexbidv
    imbi12d
    @27
    @25
    c0
    com
    wcel
    c0
    c0
    wceq
    #
    @27
    peano1
    c0
    eqid
    @26
    @44
    vx
    c0
    com
    @0
    c0
    wceq
    #
    @1
    c0
    c0
    @45
    @1
    c2o
    c0
    comu
    co
    c0
    @0
    c0
    c2o
    comu
    oveq2
    c2o
    om0x
    syl6eq
    eqeq2d
    rspcev
    mp2an
    a1i
    @28
    com
    wcel
    #
    @39
    @34
    wn
    @35
    @31
    @46
    @34
    @38
    @34
    @28
    @9
    wceq
    #
    vy
    com
    wrex
    #
    @46
    @38
    @33
    @47
    vx
    vy
    com
    @11
    @1
    @9
    @28
    @12
    eqeq2d
    cbvrexv
    @48
    @38
    wi
    @46
    @47
    @38
    vy
    com
    @13
    @38
    @47
    @9
    csuc
    #
    csuc
    #
    @1
    wceq
    #
    vx
    com
    wrex
    #
    @13
    @16
    com
    wcel
    @50
    c2o
    @16
    comu
    co
    #
    wceq
    #
    @52
    @8
    peano2
    @13
    @53
    @9
    c2o
    coa
    co
    #
    @9
    c1o
    coa
    co
    #
    csuc
    #
    @50
    c2o
    com
    wcel
    #
    @13
    @53
    @55
    wceq
    2onn
    c2o
    @8
    nnmsuc
    mpan
    @13
    @55
    @9
    c1o
    csuc
    #
    coa
    co
    #
    @57
    c2o
    @59
    @9
    coa
    df-2o
    oveq2i
    @13
    @9
    com
    wcel
    #
    c1o
    com
    wcel
    @60
    @57
    wceq
    @58
    @13
    @61
    2onn
    c2o
    @8
    nnmcl
    mpan
    #
    1onn
    @9
    c1o
    nnasuc
    sylancl
    syl5req
    @13
    @61
    @9
    con0
    wcel
    @56
    @49
    wceq
    @57
    @50
    wceq
    @62
    @9
    nnon
    @9
    oa1suc
    @56
    @49
    suceq
    4syl
    3eqtr2rd
    @51
    @54
    vx
    @16
    com
    @0
    @16
    wceq
    @1
    @53
    @50
    @0
    @16
    c2o
    comu
    oveq2
    eqeq2d
    rspcev
    syl2anc
    @47
    @37
    @51
    vx
    com
    @47
    @36
    @50
    @1
    @47
    @29
    @49
    wceq
    @36
    @50
    wceq
    @28
    @9
    suceq
    @29
    @49
    suceq
    syl
    eqeq1d
    rexbidv
    syl5ibrcom
    rexlimiv
    a1i
    syl5bi
    con3d
    @31
    @34
    con1
    syl9
    finds
    impbid2
end
