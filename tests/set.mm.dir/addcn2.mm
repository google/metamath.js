include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "rphalfcl.mm"
include "3ad2ant1.mm"
include "simprl.mm"
include "simpl2.mm"
include "simprr.mm"
include "pnpcan2d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "simpl3.mm"
include "pnpcand.mm"
include "anbi12d.mm"
include "cr.mm"
include "addcl.mm"
include "adantl.mm"
include "addcld.mm"
include "simpl1.mm"
include "rpred.mm"
include "abs3lem.mm"
include "syl22anc.mm"
include "sylbird.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi1d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "anbi2d.mm"
include "rspc2ev.mm"
include "syl3anc.mm"

theorem addcn2
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let cT: class T

  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint B z
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint C z
  disjoint u w
  disjoint v w
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint T y
  disjoint T z
  assert |- ( ( A e. RR+ /\ B e. CC /\ C e. CC ) -> E. y e. RR+ E. z e. RR+ A. u e. CC A. v e. CC ( ( ( abs ` ( u - B ) ) < y /\ ( abs ` ( v - C ) ) < z ) -> ( abs ` ( ( u + v ) - ( B + C ) ) ) < A ) )

  proof
    cA
    crp
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cA
    c2
    cdiv
    co
    #
    crp
    wcel
    #
    @5
    vu
    cv
    #
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    vv
    cv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    wa
    #
    @6
    @10
    caddc
    co
    #
    cB
    cC
    caddc
    co
    #
    cmin
    co
    cabs
    cfv
    cA
    clt
    wbr
    #
    wi
    #
    vv
    cc
    wral
    vu
    cc
    wral
    #
    @8
    vy
    cv
    #
    clt
    wbr
    #
    @12
    vz
    cv
    #
    clt
    wbr
    #
    wa
    #
    @17
    wi
    #
    vv
    cc
    wral
    vu
    cc
    wral
    #
    vz
    crp
    wrex
    vy
    crp
    wrex
    @0
    @1
    @5
    @2
    cA
    rphalfcl
    3ad2ant1
    #
    @27
    @3
    @18
    vu
    vv
    cc
    cc
    @3
    @6
    cc
    wcel
    #
    @10
    cc
    wcel
    #
    wa
    #
    wa
    #
    @14
    @15
    cB
    @10
    caddc
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    @32
    @16
    cmin
    co
    #
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    wa
    #
    @17
    @31
    @35
    @9
    @38
    @13
    @31
    @34
    @8
    @4
    clt
    @31
    @33
    @7
    cabs
    @31
    @6
    cB
    @10
    @3
    @28
    @29
    simprl
    @0
    @1
    @2
    @30
    simpl2
    #
    @3
    @28
    @29
    simprr
    #
    pnpcan2d
    fveq2d
    breq1d
    @31
    @37
    @12
    @4
    clt
    @31
    @36
    @11
    cabs
    @31
    cB
    @10
    cC
    @40
    @41
    @0
    @1
    @2
    @30
    simpl3
    #
    pnpcand
    fveq2d
    breq1d
    anbi12d
    @31
    @15
    cc
    wcel
    #
    @16
    cc
    wcel
    @32
    cc
    wcel
    cA
    cr
    wcel
    @39
    @17
    wi
    @30
    @43
    @3
    @6
    @10
    addcl
    adantl
    @31
    cB
    cC
    @40
    @42
    addcld
    @31
    cB
    @10
    @40
    @41
    addcld
    @31
    cA
    @0
    @1
    @2
    @30
    simpl1
    rpred
    @15
    @16
    @32
    cA
    abs3lem
    syl22anc
    sylbird
    ralrimivva
    @26
    @19
    @9
    @23
    wa
    #
    @17
    wi
    #
    vv
    cc
    wral
    vu
    cc
    wral
    vy
    vz
    @4
    @4
    crp
    crp
    @20
    @4
    wceq
    #
    @25
    @45
    vu
    vv
    cc
    cc
    @46
    @24
    @44
    @17
    @46
    @21
    @9
    @23
    @20
    @4
    @8
    clt
    breq2
    anbi1d
    imbi1d
    2ralbidv
    @22
    @4
    wceq
    #
    @45
    @18
    vu
    vv
    cc
    cc
    @47
    @44
    @14
    @17
    @47
    @23
    @13
    @9
    @22
    @4
    @12
    clt
    breq2
    anbi2d
    imbi1d
    2ralbidv
    rspc2ev
    syl3anc
end
