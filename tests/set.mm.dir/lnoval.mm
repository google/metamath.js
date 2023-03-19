include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "clno.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "cmap.mm"
include "crab.mm"
include "cns.mm"
include "cpv.mm"
include "cba.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "oveqd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "2ralbidv.mm"
include "df-lno.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2.mm"
include "syl5eq.mm"

theorem lnoval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cR: class R
  let cS: class S
  let cU: class U
  let cG: class G
  let cH: class H
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vw: setvar w
  let cT: class T
  assume lnoval.1: |- X = ( BaseSet ` U )
  assume lnoval.2: |- Y = ( BaseSet ` W )
  assume lnoval.3: |- G = ( +v ` U )
  assume lnoval.4: |- H = ( +v ` W )
  assume lnoval.5: |- R = ( .sOLD ` U )
  assume lnoval.6: |- S = ( .sOLD ` W )
  assume lnoval.7: |- L = ( U LnOp W )

  disjoint t x
  disjoint t y
  disjoint t z
  disjoint U t
  disjoint x y
  disjoint x z
  disjoint U x
  disjoint y z
  disjoint U y
  disjoint U z
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint X t
  disjoint X y
  disjoint X z
  disjoint Y t
  disjoint G t
  disjoint R t
  disjoint H t
  disjoint S t
  disjoint t u
  disjoint t w
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint U u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint U w
  disjoint W u
  disjoint W w
  disjoint X u
  disjoint X w
  disjoint Y u
  disjoint Y w
  disjoint G u
  disjoint G w
  disjoint R u
  disjoint R w
  disjoint H u
  disjoint H w
  disjoint S u
  disjoint S w
  disjoint T t
  disjoint T u
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> L = { t e. ( Y ^m X ) | A. x e. CC A. y e. X A. z e. X ( t ` ( ( x R y ) G z ) ) = ( ( x S ( t ` y ) ) H ( t ` z ) ) } )

  proof
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    wa
    cL
    cU
    cW
    clno
    co
    vx
    cv
    #
    vy
    cv
    #
    cR
    co
    #
    vz
    cv
    #
    cG
    co
    #
    vt
    cv
    #
    cfv
    #
    @0
    @1
    @5
    cfv
    #
    cS
    co
    #
    @3
    @5
    cfv
    #
    cH
    co
    #
    wceq
    #
    vz
    cX
    wral
    vy
    cX
    wral
    #
    vx
    cc
    wral
    #
    vt
    cY
    cX
    cmap
    co
    #
    crab
    #
    lnoval.7
    vu
    vw
    cU
    cW
    cnv
    cnv
    @0
    @1
    vu
    cv
    #
    cns
    cfv
    #
    co
    #
    @3
    @16
    cpv
    cfv
    #
    co
    #
    @5
    cfv
    #
    @0
    @7
    vw
    cv
    #
    cns
    cfv
    #
    co
    #
    @9
    @22
    cpv
    cfv
    #
    co
    #
    wceq
    #
    vz
    @16
    cba
    cfv
    #
    wral
    #
    vy
    @28
    wral
    #
    vx
    cc
    wral
    #
    vt
    @22
    cba
    cfv
    #
    @28
    cmap
    co
    #
    crab
    @15
    clno
    @6
    @26
    wceq
    #
    vz
    cX
    wral
    #
    vy
    cX
    wral
    #
    vx
    cc
    wral
    #
    vt
    @32
    cX
    cmap
    co
    #
    crab
    @16
    cU
    wceq
    #
    @31
    @37
    vt
    @33
    @38
    @39
    @28
    cX
    @32
    cmap
    @39
    @28
    cU
    cba
    cfv
    cX
    @16
    cU
    cba
    fveq2
    lnoval.1
    syl6eqr
    #
    oveq2d
    @39
    @30
    @36
    vx
    cc
    @39
    @29
    @35
    vy
    @28
    cX
    @40
    @39
    @27
    @34
    vz
    @28
    cX
    @40
    @39
    @21
    @6
    @26
    @39
    @20
    @4
    @5
    @39
    @18
    @2
    @3
    @3
    @19
    cG
    @39
    @19
    cU
    cpv
    cfv
    cG
    @16
    cU
    cpv
    fveq2
    lnoval.3
    syl6eqr
    @39
    @17
    cR
    @0
    @1
    @39
    @17
    cU
    cns
    cfv
    cR
    @16
    cU
    cns
    fveq2
    lnoval.5
    syl6eqr
    oveqd
    @39
    @3
    eqidd
    oveq123d
    fveq2d
    eqeq1d
    raleqbidv
    raleqbidv
    ralbidv
    rabeqbidv
    @22
    cW
    wceq
    #
    @37
    @13
    vt
    @38
    @14
    @41
    @32
    cY
    cX
    cmap
    @41
    @32
    cW
    cba
    cfv
    cY
    @22
    cW
    cba
    fveq2
    lnoval.2
    syl6eqr
    oveq1d
    @41
    @36
    @12
    vx
    cc
    @41
    @34
    @11
    vy
    vz
    cX
    cX
    @41
    @26
    @10
    @6
    @41
    @24
    @8
    @9
    @9
    @25
    cH
    @41
    @25
    cW
    cpv
    cfv
    cH
    @22
    cW
    cpv
    fveq2
    lnoval.4
    syl6eqr
    @41
    @23
    cS
    @0
    @7
    @41
    @23
    cW
    cns
    cfv
    cS
    @22
    cW
    cns
    fveq2
    lnoval.6
    syl6eqr
    oveqd
    @41
    @9
    eqidd
    oveq123d
    eqeq2d
    2ralbidv
    ralbidv
    rabeqbidv
    vx
    vy
    vz
    vw
    vu
    vt
    df-lno
    @13
    vt
    @14
    cY
    cX
    cmap
    ovex
    rabex
    ovmpt2
    syl5eq
end
