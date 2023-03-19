include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cee.mm"
include "cop.mm"
include "cds.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cmpt2.mm"
include "cpr.mm"
include "citv.mm"
include "cbtwn.mm"
include "wbr.mm"
include "crab.mm"
include "clng.mm"
include "csn.mm"
include "cdif.mm"
include "w3o.mm"
include "cun.mm"
include "cn.mm"
include "ceeng.mm"
include "wceq.mm"
include "fveq2.mm"
include "opeq2d.mm"
include "wcel.mm"
include "adantr.mm"
include "wa.mm"
include "simpl.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "mpt2eq123dva.mm"
include "preq12d.mm"
include "rabeqdv.mm"
include "difeq1d.mm"
include "uneq12d.mm"
include "df-eeng.mm"
include "prex.mm"
include "unex.mm"
include "fvmpt.mm"

theorem eengv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let cN: class N
  let vn: setvar n

  disjoint i x
  disjoint i y
  disjoint i z
  disjoint N i
  disjoint x y
  disjoint x z
  disjoint N x
  disjoint y z
  disjoint N y
  disjoint N z
  disjoint i n
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint N n
  assert |- ( N e. NN -> ( EEG ` N ) = ( { <. ( Base ` ndx ) , ( EE ` N ) >. , <. ( dist ` ndx ) , ( x e. ( EE ` N ) , y e. ( EE ` N ) |-> sum_ i e. ( 1 ... N ) ( ( ( x ` i ) - ( y ` i ) ) ^ 2 ) ) >. } u. { <. ( Itv ` ndx ) , ( x e. ( EE ` N ) , y e. ( EE ` N ) |-> { z e. ( EE ` N ) | z Btwn <. x , y >. } ) >. , <. ( LineG ` ndx ) , ( x e. ( EE ` N ) , y e. ( ( EE ` N ) \ { x } ) |-> { z e. ( EE ` N ) | ( z Btwn <. x , y >. \/ x Btwn <. z , y >. \/ y Btwn <. x , z >. ) } ) >. } ) )

  proof
    vn
    cN
    cnx
    cbs
    cfv
    #
    vn
    cv
    #
    cee
    cfv
    #
    cop
    #
    cnx
    cds
    cfv
    #
    vx
    vy
    @2
    @2
    c1
    @1
    cfz
    co
    #
    vi
    cv
    #
    vx
    cv
    #
    cfv
    @6
    vy
    cv
    #
    cfv
    cmin
    co
    c2
    cexp
    co
    #
    vi
    csu
    #
    cmpt2
    #
    cop
    #
    cpr
    #
    cnx
    citv
    cfv
    #
    vx
    vy
    @2
    @2
    vz
    cv
    #
    @7
    @8
    cop
    cbtwn
    wbr
    #
    vz
    @2
    crab
    #
    cmpt2
    #
    cop
    #
    cnx
    clng
    cfv
    #
    vx
    vy
    @2
    @2
    @7
    csn
    #
    cdif
    #
    @16
    @7
    @15
    @8
    cop
    cbtwn
    wbr
    @8
    @7
    @15
    cop
    cbtwn
    wbr
    w3o
    #
    vz
    @2
    crab
    #
    cmpt2
    #
    cop
    #
    cpr
    #
    cun
    @0
    cN
    cee
    cfv
    #
    cop
    #
    @4
    vx
    vy
    @28
    @28
    c1
    cN
    cfz
    co
    #
    @9
    vi
    csu
    #
    cmpt2
    #
    cop
    #
    cpr
    #
    @14
    vx
    vy
    @28
    @28
    @16
    vz
    @28
    crab
    #
    cmpt2
    #
    cop
    #
    @20
    vx
    vy
    @28
    @28
    @21
    cdif
    #
    @23
    vz
    @28
    crab
    #
    cmpt2
    #
    cop
    #
    cpr
    #
    cun
    cn
    ceeng
    @1
    cN
    wceq
    #
    @13
    @34
    @27
    @42
    @43
    @3
    @29
    @12
    @33
    @43
    @2
    @28
    @0
    @1
    cN
    cee
    fveq2
    #
    opeq2d
    @43
    @11
    @32
    @4
    @43
    vx
    vy
    @2
    @2
    @10
    @28
    @28
    @31
    @44
    @43
    @2
    @28
    wceq
    #
    @7
    @2
    wcel
    #
    @44
    adantr
    #
    @43
    @46
    @8
    @2
    wcel
    wa
    #
    wa
    #
    @5
    @30
    @9
    vi
    @49
    @1
    cN
    c1
    cfz
    @43
    @48
    simpl
    oveq2d
    sumeq1d
    mpt2eq123dva
    opeq2d
    preq12d
    @43
    @19
    @37
    @26
    @41
    @43
    @18
    @36
    @14
    @43
    vx
    vy
    @2
    @2
    @17
    @28
    @28
    @35
    @44
    @47
    @49
    @16
    vz
    @2
    @28
    @43
    @45
    @48
    @44
    adantr
    rabeqdv
    mpt2eq123dva
    opeq2d
    @43
    @25
    @40
    @20
    @43
    vx
    vy
    @2
    @22
    @24
    @28
    @38
    @39
    @44
    @43
    @46
    wa
    @2
    @28
    @21
    @47
    difeq1d
    @43
    @24
    @39
    wceq
    @46
    @8
    @22
    wcel
    wa
    @43
    @23
    vz
    @2
    @28
    @44
    rabeqdv
    adantr
    mpt2eq123dva
    opeq2d
    preq12d
    uneq12d
    vx
    vy
    vz
    vi
    vn
    df-eeng
    @34
    @42
    @29
    @33
    prex
    @37
    @41
    prex
    unex
    fvmpt
end
