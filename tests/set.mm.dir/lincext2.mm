include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cvv.mm"
include "cdm.mm"
include "cfn.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "fvex.mm"
include "ifex.mm"
include "dmmpti.mm"
include "difeq1i.mm"
include "wss.mm"
include "snssi.mm"
include "3ad2ant2.mm"
include "dfss4.mm"
include "sylib.mm"
include "snfi.mm"
include "syl6eqel.mm"
include "syl5eqel.mm"
include "lincext1.mm"
include "3adant3.mm"
include "wfun.mm"
include "elmapfun.mm"
include "syl.mm"
include "cres.mm"
include "wf.mm"
include "elmapi.mm"
include "fdmdifeqresdif.mm"
include "3ad2ant3.mm"
include "simp3.mm"
include "c0g.mm"
include "eqeltri.mm"
include "a1i.mm"
include "resfsupp.mm"

theorem lincext2
  let vz: setvar z
  let cB: class B
  let cR: class R
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume lincext.b: |- B = ( Base ` M )
  assume lincext.r: |- R = ( Scalar ` M )
  assume lincext.e: |- E = ( Base ` R )
  assume lincext.0: |- .0. = ( 0g ` R )
  assume lincext.z: |- Z = ( 0g ` M )
  assume lincext.n: |- N = ( invg ` R )
  assume lincext.f: |- F = ( z e. S |-> if ( z = X , ( N ` Y ) , ( G ` z ) ) )

  disjoint B z
  disjoint E z
  disjoint G z
  disjoint M z
  disjoint S z
  disjoint X z
  disjoint Y z
  disjoint k x
  assert |- ( ( ( M e. LMod /\ S e. ~P B ) /\ ( Y e. E /\ X e. S /\ G e. ( E ^m ( S \ { X } ) ) ) /\ G finSupp .0. ) -> F finSupp .0. )

  proof
    cM
    clmod
    wcel
    cS
    cB
    cpw
    wcel
    wa
    #
    cY
    cE
    wcel
    #
    cX
    cS
    wcel
    #
    cG
    cE
    cS
    cX
    csn
    #
    cdif
    #
    cmap
    co
    wcel
    #
    w3a
    #
    cG
    c.0
    cfsupp
    wbr
    #
    w3a
    #
    @4
    cF
    cG
    cvv
    cE
    cS
    cmap
    co
    #
    c.0
    @8
    cF
    cdm
    #
    @4
    cdif
    cS
    @4
    cdif
    #
    cfn
    @10
    cS
    @4
    vz
    cS
    vz
    cv
    #
    cX
    wceq
    #
    cY
    cN
    cfv
    #
    @12
    cG
    cfv
    #
    cif
    cF
    @13
    @14
    @15
    cY
    cN
    fvex
    @12
    cG
    fvex
    ifex
    lincext.f
    dmmpti
    difeq1i
    @8
    @11
    @3
    cfn
    @8
    @3
    cS
    wss
    #
    @11
    @3
    wceq
    @6
    @0
    @16
    @7
    @2
    @1
    @16
    @5
    cX
    cS
    snssi
    3ad2ant2
    3ad2ant2
    @3
    cS
    dfss4
    sylib
    cX
    snfi
    syl6eqel
    syl5eqel
    @0
    @6
    cF
    @9
    wcel
    #
    @7
    vz
    cB
    cR
    cS
    cE
    cF
    cG
    cM
    cN
    cX
    cY
    c.0
    cZ
    lincext.b
    lincext.r
    lincext.e
    lincext.0
    lincext.z
    lincext.n
    lincext.f
    lincext1
    3adant3
    #
    @8
    @17
    cF
    wfun
    @18
    cF
    cE
    cS
    elmapfun
    syl
    @6
    @0
    cG
    cF
    @4
    cres
    wceq
    #
    @7
    @5
    @1
    @19
    @2
    @5
    @4
    cE
    cG
    wf
    @19
    cG
    cE
    @4
    elmapi
    vz
    cS
    cE
    cF
    cG
    @14
    cX
    lincext.f
    fdmdifeqresdif
    syl
    3ad2ant3
    3ad2ant2
    @0
    @6
    @7
    simp3
    c.0
    cvv
    wcel
    @8
    c.0
    cR
    c0g
    cfv
    cvv
    lincext.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    resfsupp
end
