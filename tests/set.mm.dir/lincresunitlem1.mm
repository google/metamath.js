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
include "simpr.mm"
include "unitnegcl.mm"
include "syl2an.mm"
include "ringinvcl.mm"
include "syl2anc.mm"

theorem lincresunitlem1
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


  assert |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S ) /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U ) ) -> ( I ` ( N ` ( F ` X ) ) ) e. E )

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
    cR
    crg
    wcel
    #
    @5
    cN
    cfv
    #
    cU
    wcel
    #
    @9
    cI
    cfv
    cE
    wcel
    @3
    @8
    @7
    @1
    @0
    @8
    @2
    cR
    cM
    lincresunit.r
    lmodring
    3ad2ant2
    #
    adantr
    @3
    @8
    @6
    @10
    @7
    @11
    @4
    @6
    simpr
    cR
    cU
    cN
    @5
    lincresunit.u
    lincresunit.n
    unitnegcl
    syl2an
    cE
    cR
    cU
    cI
    @9
    lincresunit.u
    lincresunit.i
    lincresunit.e
    ringinvcl
    syl2anc
end
