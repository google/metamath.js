include "cpw.mm"
include "wcel.mm"
include "clmod.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "wa.mm"
include "crg.mm"
include "lmodring.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "lincresunitlem1.mm"
include "wi.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl.mm"
include "ad2antrl.mm"
include "imp.mm"
include "ringcl.mm"
include "syl3anc.mm"

theorem lincresunitlem2
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
  let cY: class Y
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


  assert |- ( ( ( ( S e. ~P B /\ M e. LMod /\ X e. S ) /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U ) ) /\ Y e. S ) -> ( ( I ` ( N ` ( F ` X ) ) ) .x. ( F ` Y ) ) e. E )

  proof
    cS
    cB
    cpw
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
    #
    cX
    cF
    cfv
    #
    cU
    wcel
    #
    wa
    #
    wa
    #
    cY
    cS
    wcel
    #
    wa
    cR
    crg
    wcel
    #
    @5
    cN
    cfv
    cI
    cfv
    #
    cE
    wcel
    #
    cY
    cF
    cfv
    #
    cE
    wcel
    #
    @11
    @13
    c.x
    co
    cE
    wcel
    @8
    @10
    @9
    @3
    @10
    @7
    @1
    @0
    @10
    @2
    cR
    cM
    lincresunit.r
    lmodring
    3ad2ant2
    adantr
    adantr
    @8
    @12
    @9
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
    lincresunitlem1
    adantr
    @8
    @9
    @14
    @4
    @9
    @14
    wi
    #
    @3
    @6
    @4
    cS
    cE
    cF
    wf
    #
    @15
    cF
    cE
    cS
    elmapi
    @16
    @9
    @14
    cS
    cE
    cY
    cF
    ffvelrn
    ex
    syl
    ad2antrl
    imp
    cE
    cR
    c.x
    @11
    @13
    lincresunit.e
    lincresunit.t
    ringcl
    syl3anc
end
