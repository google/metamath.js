include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "c1.mm"
include "cdiv.mm"
include "cpi.mm"
include "cneg.mm"
include "cpr.mm"
include "cmul.mm"
include "simp1l.mm"
include "1cnd.mm"
include "simp2l.mm"
include "simp1r.mm"
include "divcld.mm"
include "subdid.mm"
include "mulid1d.mm"
include "divcan2d.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "wceq.mm"
include "subcld.mm"
include "simp3.mm"
include "necomd.mm"
include "divne1d.mm"
include "subne0d.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "angcan.mm"
include "syl222anc.mm"
include "eqtr3d.mm"
include "simp2r.mm"
include "divne0d.mm"
include "ang180lem4.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem ang180lem5
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cC: class C
  assume ang.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) /\ A =/= B ) -> ( ( ( ( A - B ) F A ) + ( B F ( B - A ) ) ) + ( A F B ) ) e. { -u _pi , _pi } )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cB
    cmin
    co
    #
    cA
    cF
    co
    #
    cB
    cB
    cA
    cmin
    co
    #
    cF
    co
    #
    caddc
    co
    #
    cA
    cB
    cF
    co
    #
    caddc
    co
    c1
    cB
    cA
    cdiv
    co
    #
    cmin
    co
    #
    c1
    cF
    co
    #
    @14
    @14
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
    @14
    cF
    co
    #
    caddc
    co
    #
    cpi
    cneg
    cpi
    cpr
    #
    @7
    @12
    @19
    @13
    @20
    caddc
    @7
    @9
    @16
    @11
    @18
    caddc
    @7
    cA
    @15
    cmul
    co
    #
    cA
    c1
    cmul
    co
    #
    cF
    co
    #
    @9
    @16
    @7
    @23
    @8
    @24
    cA
    cF
    @7
    @23
    @24
    cA
    @14
    cmul
    co
    #
    cmin
    co
    @8
    @7
    cA
    c1
    @14
    @0
    @1
    @5
    @6
    simp1l
    #
    @7
    1cnd
    #
    @7
    cB
    cA
    @2
    @3
    @4
    @6
    simp2l
    #
    @27
    @0
    @1
    @5
    @6
    simp1r
    #
    divcld
    #
    subdid
    @7
    @24
    cA
    @26
    cB
    cmin
    @7
    cA
    @27
    mulid1d
    #
    @7
    cB
    cA
    @29
    @27
    @30
    divcan2d
    #
    oveq12d
    eqtrd
    @32
    oveq12d
    @7
    @15
    cc
    wcel
    @15
    cc0
    wne
    c1
    cc
    wcel
    #
    c1
    cc0
    wne
    #
    @0
    @1
    @25
    @16
    wceq
    @7
    c1
    @14
    @28
    @31
    subcld
    @7
    c1
    @14
    @28
    @31
    @7
    @14
    c1
    @7
    cB
    cA
    @29
    @27
    @30
    @7
    cA
    cB
    @2
    @5
    @6
    simp3
    necomd
    divne1d
    #
    necomd
    subne0d
    @28
    @35
    @7
    ax-1ne0
    a1i
    #
    @27
    @30
    vx
    vy
    @15
    c1
    cA
    cF
    ang.1
    angcan
    syl222anc
    eqtr3d
    @7
    @26
    cA
    @17
    cmul
    co
    #
    cF
    co
    #
    @11
    @18
    @7
    @26
    cB
    @38
    @10
    cF
    @33
    @7
    @38
    @26
    @24
    cmin
    co
    @10
    @7
    cA
    @14
    c1
    @27
    @31
    @28
    subdid
    @7
    @26
    cB
    @24
    cA
    cmin
    @33
    @32
    oveq12d
    eqtrd
    oveq12d
    @7
    @14
    cc
    wcel
    #
    @14
    cc0
    wne
    #
    @17
    cc
    wcel
    @17
    cc0
    wne
    @0
    @1
    @39
    @18
    wceq
    @31
    @7
    cB
    cA
    @29
    @27
    @2
    @3
    @4
    @6
    simp2r
    @30
    divne0d
    #
    @7
    @14
    c1
    @31
    @28
    subcld
    @7
    @14
    c1
    @31
    @28
    @36
    subne0d
    @27
    @30
    vx
    vy
    @14
    @17
    cA
    cF
    ang.1
    angcan
    syl222anc
    eqtr3d
    oveq12d
    @7
    @24
    @26
    cF
    co
    #
    @13
    @20
    @7
    @24
    cA
    @26
    cB
    cF
    @32
    @33
    oveq12d
    @7
    @34
    @35
    @40
    @41
    @0
    @1
    @43
    @20
    wceq
    @28
    @37
    @31
    @42
    @27
    @30
    vx
    vy
    c1
    @14
    cA
    cF
    ang.1
    angcan
    syl222anc
    eqtr3d
    oveq12d
    @7
    @40
    @41
    @14
    c1
    wne
    @21
    @22
    wcel
    @31
    @42
    @36
    vx
    vy
    @14
    cF
    ang.1
    ang180lem4
    syl3anc
    eqeltrd
end
