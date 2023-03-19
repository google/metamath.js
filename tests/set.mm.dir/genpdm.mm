include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cvv.mm"
include "wcel.mm"
include "cnp.mm"
include "wral.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "wa.mm"
include "cnq.mm"
include "wss.mm"
include "wi.mm"
include "elprnq.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "syl2an.mm"
include "an4s.mm"
include "rexlimdvva.mm"
include "abssdv.mm"
include "nqex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "rgen2a.mm"
include "fnmpt2.mm"
include "fndm.mm"
include "mp2b.mm"

theorem genpdm
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume genp.1: |- F = ( w e. P. , v e. P. |-> { x | E. y e. w E. z e. v x = ( y G z ) } )
  assume genp.2: |- ( ( y e. Q. /\ z e. Q. ) -> ( y G z ) e. Q. )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint v x
  disjoint G x
  disjoint w y
  disjoint v y
  disjoint G y
  disjoint w z
  disjoint v z
  disjoint G z
  disjoint v w
  disjoint G w
  disjoint G v
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint A x
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint A y
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint A z
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint F f
  disjoint F g
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint D g
  disjoint D h
  assert |- dom F = ( P. X. P. )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cG
    co
    #
    wceq
    #
    vz
    vv
    cv
    #
    wrex
    vy
    vw
    cv
    #
    wrex
    #
    vx
    cab
    #
    cvv
    wcel
    #
    vv
    cnp
    wral
    vw
    cnp
    wral
    cF
    cnp
    cnp
    cxp
    #
    wfn
    cF
    cdm
    @10
    wceq
    @9
    vw
    vv
    cnp
    @6
    cnp
    wcel
    #
    @5
    cnp
    wcel
    #
    wa
    #
    @8
    cnq
    wss
    cnq
    cvv
    wcel
    @9
    @13
    @7
    vx
    cnq
    @13
    @4
    @0
    cnq
    wcel
    #
    vy
    vz
    @6
    @5
    @11
    @1
    @6
    wcel
    #
    @12
    @2
    @5
    wcel
    #
    @4
    @14
    wi
    #
    @11
    @15
    wa
    @1
    cnq
    wcel
    #
    @2
    cnq
    wcel
    #
    @17
    @12
    @16
    wa
    @6
    @1
    elprnq
    @5
    @2
    elprnq
    @18
    @19
    wa
    @14
    @4
    @3
    cnq
    wcel
    genp.2
    @0
    @3
    cnq
    eleq1
    syl5ibrcom
    syl2an
    an4s
    rexlimdvva
    abssdv
    nqex
    @8
    cnq
    cvv
    ssexg
    sylancl
    rgen2a
    vw
    vv
    cnp
    cnp
    @8
    cF
    cvv
    genp.1
    fnmpt2
    @10
    cF
    fndm
    mp2b
end
