include "com.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "ccrd.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "inss2.mm"
include "sseli.mm"
include "wel.mm"
include "wa.mm"
include "snfi.mm"
include "inss1.mm"
include "elpwid.mm"
include "con0.mm"
include "onfin2.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "sselda.mm"
include "pwfi.mm"
include "sylib.mm"
include "xpfi.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "iunfi.mm"
include "syl2anc.mm"
include "ficardom.mm"
include "syl.mm"
include "fmpti.mm"

theorem ackbij1lem10
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  let cA: class A
  let cB: class B
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint B y
  assert |- F : ( ~P _om i^i Fin ) --> _om

  proof
    vx
    com
    cpw
    #
    cfn
    cin
    #
    com
    vy
    vx
    cv
    #
    vy
    cv
    #
    csn
    #
    @3
    cpw
    #
    cxp
    #
    ciun
    #
    ccrd
    cfv
    #
    cF
    ackbij.f
    @2
    @1
    wcel
    #
    @7
    cfn
    wcel
    #
    @8
    com
    wcel
    @9
    @2
    cfn
    wcel
    @6
    cfn
    wcel
    #
    vy
    @2
    wral
    @10
    @1
    cfn
    @2
    @0
    cfn
    inss2
    sseli
    @9
    @11
    vy
    @2
    @9
    vy
    vx
    wel
    wa
    #
    @4
    cfn
    wcel
    @5
    cfn
    wcel
    #
    @11
    @3
    snfi
    @12
    @3
    cfn
    wcel
    @13
    @9
    @2
    cfn
    @3
    @9
    @2
    com
    cfn
    @9
    @2
    com
    @1
    @0
    @2
    @0
    cfn
    inss1
    sseli
    elpwid
    com
    con0
    cfn
    cin
    cfn
    onfin2
    con0
    cfn
    inss2
    eqsstri
    syl6ss
    sselda
    @3
    pwfi
    sylib
    @4
    @5
    xpfi
    sylancr
    ralrimiva
    vy
    @2
    @6
    iunfi
    syl2anc
    @7
    ficardom
    syl
    fmpti
end
