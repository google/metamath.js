include "cpw.mm"
include "wcel.mm"
include "clmod.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmpt.mm"
include "wf.mm"
include "eldifi.mm"
include "lincresunitlem2.mm"
include "sylan2.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "syl5eqel.mm"

theorem lincresunit1
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume lincresunit.b: |- B = ( Base ` M )
  assume lincresunit.r: |- R = ( Scalar ` M )
  assume lincresunit.e: |- E = ( Base ` R )
  assume lincresunit.u: |- U = ( Unit ` R )
  assume lincresunit.0: |- .0. = ( 0g ` R )
  assume lincresunit.z: |- Z = ( 0g ` M )
  assume lincresunit.n: |- N = ( invg ` R )
  assume lincresunit.i: |- I = ( invr ` R )
  assume lincresunit.t: |- .x. = ( .r ` R )
  assume lincresunit.g: |- G = ( s e. ( S \ { X } ) |-> ( ( I ` ( N ` ( F ` X ) ) ) .x. ( F ` s ) ) )

  disjoint B s
  disjoint E s
  disjoint F s
  disjoint M s
  disjoint S s
  disjoint X s
  disjoint U s
  disjoint k x
  assert |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S ) /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U ) ) -> G e. ( E ^m ( S \ { X } ) ) )

  proof
    cS
    cB
    cpw
    #
    wcel
    #
    cM
    clmod
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cF
    cE
    cS
    cmap
    co
    wcel
    cX
    cF
    cfv
    #
    cU
    wcel
    wa
    #
    wa
    #
    cG
    vs
    cS
    cX
    csn
    #
    cdif
    #
    @5
    cN
    cfv
    cI
    cfv
    vs
    cv
    #
    cF
    cfv
    c.x
    co
    #
    cmpt
    #
    cE
    @9
    cmap
    co
    #
    lincresunit.g
    @7
    @12
    @13
    wcel
    #
    @9
    cE
    @12
    wf
    #
    @7
    vs
    @9
    @11
    cE
    @12
    @10
    @9
    wcel
    @7
    @10
    cS
    wcel
    @11
    cE
    wcel
    @10
    cS
    @8
    eldifi
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    @10
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunitlem2
    sylan2
    @12
    eqid
    fmptd
    @7
    cE
    cvv
    wcel
    @9
    cvv
    wcel
    #
    @14
    @15
    wb
    cE
    cR
    cbs
    cfv
    cvv
    lincresunit.e
    cR
    cbs
    fvex
    eqeltri
    @4
    @16
    @6
    @1
    @2
    @16
    @3
    cS
    @8
    @0
    difexg
    3ad2ant1
    adantr
    cE
    @9
    @12
    cvv
    cvv
    elmapg
    sylancr
    mpbird
    syl5eqel
end
