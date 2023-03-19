include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "cpi.mm"
include "cneg.mm"
include "cpr.mm"
include "1cnd.mm"
include "simp1.mm"
include "subcld.mm"
include "simp3.mm"
include "necomd.mm"
include "subne0d.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "angvald.mm"
include "simp2.mm"
include "oveq12d.mm"
include "divcld.mm"
include "recne0d.mm"
include "logcld.mm"
include "divne0d.mm"
include "imaddd.mm"
include "eqtr4d.mm"
include "div1d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "addcld.mm"
include "ci.mm"
include "cmul.mm"
include "c2.mm"
include "eqid.mm"
include "ang180lem3.mm"
include "wceq.mm"
include "wo.mm"
include "fveq2.mm"
include "ax-icn.mm"
include "picn.mm"
include "mulcli.mm"
include "imnegi.mm"
include "addid2i.mm"
include "fveq2i.mm"
include "0re.mm"
include "pire.mm"
include "crimi.mm"
include "eqtr3i.mm"
include "negeqi.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "orim12i.mm"
include "ovex.mm"
include "elpr.mm"
include "fvex.mm"
include "3imtr4i.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem ang180lem4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cB: class B
  let cC: class C
  assume ang.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( A e. CC /\ A =/= 0 /\ A =/= 1 ) -> ( ( ( ( 1 - A ) F 1 ) + ( A F ( A - 1 ) ) ) + ( 1 F A ) ) e. { -u _pi , _pi } )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cA
    c1
    wne
    #
    w3a
    #
    c1
    cA
    cmin
    co
    #
    c1
    cF
    co
    #
    cA
    cA
    c1
    cmin
    co
    #
    cF
    co
    #
    caddc
    co
    #
    c1
    cA
    cF
    co
    #
    caddc
    co
    #
    c1
    @4
    cdiv
    co
    #
    clog
    cfv
    #
    @6
    cA
    cdiv
    co
    #
    clog
    cfv
    #
    caddc
    co
    #
    cA
    clog
    cfv
    #
    caddc
    co
    #
    cim
    cfv
    #
    cpi
    cneg
    #
    cpi
    cpr
    #
    @3
    @10
    @15
    cim
    cfv
    #
    @16
    cim
    cfv
    #
    caddc
    co
    @18
    @3
    @8
    @21
    @9
    @22
    caddc
    @3
    @8
    @12
    cim
    cfv
    #
    @14
    cim
    cfv
    #
    caddc
    co
    @21
    @3
    @5
    @23
    @7
    @24
    caddc
    @3
    vx
    vy
    cF
    @4
    c1
    ang.1
    @3
    c1
    cA
    @3
    1cnd
    #
    @0
    @1
    @2
    simp1
    #
    subcld
    #
    @3
    c1
    cA
    @25
    @26
    @3
    cA
    c1
    @0
    @1
    @2
    simp3
    #
    necomd
    subne0d
    #
    @25
    c1
    cc0
    wne
    @3
    ax-1ne0
    a1i
    #
    angvald
    @3
    vx
    vy
    cF
    cA
    @6
    ang.1
    @26
    @0
    @1
    @2
    simp2
    #
    @3
    cA
    c1
    @26
    @25
    subcld
    #
    @3
    cA
    c1
    @26
    @25
    @28
    subne0d
    #
    angvald
    oveq12d
    @3
    @12
    @14
    @3
    @11
    @3
    c1
    @4
    @25
    @27
    @29
    divcld
    @3
    @4
    @27
    @29
    recne0d
    logcld
    #
    @3
    @13
    @3
    @6
    cA
    @32
    @26
    @31
    divcld
    @3
    @6
    cA
    @32
    @26
    @33
    @31
    divne0d
    logcld
    #
    imaddd
    eqtr4d
    @3
    @9
    cA
    c1
    cdiv
    co
    #
    clog
    cfv
    #
    cim
    cfv
    @22
    @3
    vx
    vy
    cF
    c1
    cA
    ang.1
    @25
    @30
    @26
    @31
    angvald
    @3
    @37
    @16
    cim
    @3
    @36
    cA
    clog
    @3
    cA
    @26
    div1d
    fveq2d
    fveq2d
    eqtrd
    oveq12d
    @3
    @15
    @16
    @3
    @12
    @14
    @34
    @35
    addcld
    @3
    cA
    @26
    @31
    logcld
    imaddd
    eqtr4d
    @3
    @17
    ci
    cpi
    cmul
    co
    #
    cneg
    #
    @38
    cpr
    wcel
    #
    @18
    @20
    wcel
    #
    vx
    vy
    cA
    @17
    cF
    @17
    ci
    cdiv
    co
    c2
    cpi
    cmul
    co
    cdiv
    co
    c1
    c2
    cdiv
    co
    cmin
    co
    #
    ang.1
    @17
    eqid
    @42
    eqid
    ang180lem3
    @17
    @39
    wceq
    #
    @17
    @38
    wceq
    #
    wo
    @18
    @19
    wceq
    #
    @18
    cpi
    wceq
    #
    wo
    @40
    @41
    @43
    @45
    @44
    @46
    @43
    @18
    @39
    cim
    cfv
    #
    @19
    @17
    @39
    cim
    fveq2
    @47
    @38
    cim
    cfv
    #
    cneg
    @19
    @38
    ci
    cpi
    ax-icn
    picn
    mulcli
    #
    imnegi
    @48
    cpi
    cc0
    @38
    caddc
    co
    #
    cim
    cfv
    @48
    cpi
    @50
    @38
    cim
    @38
    @49
    addid2i
    fveq2i
    cc0
    cpi
    0re
    pire
    crimi
    eqtr3i
    #
    negeqi
    eqtri
    syl6eq
    @44
    @18
    @48
    cpi
    @17
    @38
    cim
    fveq2
    @51
    syl6eq
    orim12i
    @17
    @39
    @38
    @15
    @16
    caddc
    ovex
    elpr
    @18
    @19
    cpi
    @17
    cim
    fvex
    elpr
    3imtr4i
    syl
    eqeltrd
end
