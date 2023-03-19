include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cdm.mm"
include "wral.mm"
include "cass.mm"
include "wcel.mm"
include "w3a.mm"
include "wi.mm"
include "wal.mm"
include "dmeq.mm"
include "dmeqd.mm"
include "eleq2d.mm"
include "3anbi123d.mm"
include "oveq.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "albidv.mm"
include "2albidv.mm"
include "r3al.mm"
include "3bitr4g.mm"
include "eqcomi.mm"
include "a1i.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "2ralbidv.mm"
include "3bitrd.mm"
include "df-ass.mm"
include "elab2g.mm"

theorem isass
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cG: class G
  let cX: class X
  let vg: setvar g
  assume isass.1: |- X = dom dom G

  disjoint G x
  disjoint G y
  disjoint G z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint G g
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint X g
  assert |- ( G e. A -> ( G e. Ass <-> A. x e. X A. y e. X A. z e. X ( ( x G y ) G z ) = ( x G ( y G z ) ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vg
    cv
    #
    co
    #
    vz
    cv
    #
    @2
    co
    #
    @0
    @1
    @4
    @2
    co
    #
    @2
    co
    #
    wceq
    #
    vz
    @2
    cdm
    #
    cdm
    #
    wral
    vy
    @10
    wral
    vx
    @10
    wral
    #
    @0
    @1
    cG
    co
    #
    @4
    cG
    co
    #
    @0
    @1
    @4
    cG
    co
    #
    cG
    co
    #
    wceq
    #
    vz
    cX
    wral
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    vg
    cG
    cass
    cA
    @2
    cG
    wceq
    #
    @11
    @16
    vz
    cG
    cdm
    #
    cdm
    #
    wral
    #
    vy
    @21
    wral
    #
    vx
    @21
    wral
    #
    @22
    vy
    cX
    wral
    #
    vx
    cX
    wral
    @18
    @19
    @0
    @10
    wcel
    #
    @1
    @10
    wcel
    #
    @4
    @10
    wcel
    #
    w3a
    #
    @8
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    @0
    @21
    wcel
    #
    @1
    @21
    wcel
    #
    @4
    @21
    wcel
    #
    w3a
    #
    @16
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    @11
    @24
    @19
    @31
    @37
    vx
    vy
    @19
    @30
    @36
    vz
    @19
    @29
    @35
    @8
    @16
    @19
    @26
    @32
    @27
    @33
    @28
    @34
    @19
    @10
    @21
    @0
    @19
    @9
    @20
    @2
    cG
    dmeq
    dmeqd
    #
    eleq2d
    @19
    @10
    @21
    @1
    @38
    eleq2d
    @19
    @10
    @21
    @4
    @38
    eleq2d
    3anbi123d
    @19
    @5
    @13
    @7
    @15
    @19
    @5
    @12
    @4
    @2
    co
    @13
    @19
    @3
    @12
    @4
    @2
    @0
    @1
    @2
    cG
    oveq
    oveq1d
    @12
    @4
    @2
    cG
    oveq
    eqtrd
    @19
    @7
    @0
    @14
    @2
    co
    @15
    @19
    @6
    @14
    @0
    @2
    @1
    @4
    @2
    cG
    oveq
    oveq2d
    @0
    @14
    @2
    cG
    oveq
    eqtrd
    eqeq12d
    imbi12d
    albidv
    2albidv
    @8
    vx
    vy
    vz
    @10
    @10
    @10
    r3al
    @16
    vx
    vy
    vz
    @21
    @21
    @21
    r3al
    3bitr4g
    @19
    @23
    @25
    vx
    @21
    cX
    @21
    cX
    wceq
    @19
    cX
    @21
    isass.1
    eqcomi
    a1i
    #
    @19
    @22
    vy
    @21
    cX
    @39
    raleqdv
    raleqbidv
    @19
    @22
    @17
    vx
    vy
    cX
    cX
    @19
    @16
    vz
    @21
    cX
    @39
    raleqdv
    2ralbidv
    3bitrd
    vx
    vy
    vz
    vg
    df-ass
    elab2g
end
