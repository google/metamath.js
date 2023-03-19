include "co.mm"
include "cfv.mm"
include "cabl.mm"
include "wcel.mm"
include "wceq.mm"
include "clmod.mm"
include "lmodabl.mm"
include "syl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "ablinvadd.mm"
include "lmodvsneg.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem lmodnegadd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lmodnegadd.v: |- V = ( Base ` W )
  assume lmodnegadd.p: |- .+ = ( +g ` W )
  assume lmodnegadd.t: |- .x. = ( .s ` W )
  assume lmodnegadd.n: |- N = ( invg ` W )
  assume lmodnegadd.r: |- R = ( Scalar ` W )
  assume lmodnegadd.k: |- K = ( Base ` R )
  assume lmodnegadd.i: |- I = ( invg ` R )
  assume lmodnegadd.w: |- ( ph -> W e. LMod )
  assume lmodnegadd.a: |- ( ph -> A e. K )
  assume lmodnegadd.b: |- ( ph -> B e. K )
  assume lmodnegadd.x: |- ( ph -> X e. V )
  assume lmodnegadd.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( N ` ( ( A .x. X ) .+ ( B .x. Y ) ) ) = ( ( ( I ` A ) .x. X ) .+ ( ( I ` B ) .x. Y ) ) )

  proof
    wph
    cA
    cX
    c.x
    co
    #
    cB
    cY
    c.x
    co
    #
    c.pl
    co
    cN
    cfv
    #
    @0
    cN
    cfv
    #
    @1
    cN
    cfv
    #
    c.pl
    co
    #
    cA
    cI
    cfv
    cX
    c.x
    co
    #
    cB
    cI
    cfv
    cY
    c.x
    co
    #
    c.pl
    co
    wph
    cW
    cabl
    wcel
    #
    @0
    cV
    wcel
    #
    @1
    cV
    wcel
    #
    @2
    @5
    wceq
    wph
    cW
    clmod
    wcel
    #
    @8
    lmodnegadd.w
    cW
    lmodabl
    syl
    wph
    @11
    cA
    cK
    wcel
    cX
    cV
    wcel
    @9
    lmodnegadd.w
    lmodnegadd.a
    lmodnegadd.x
    cA
    c.x
    cR
    cK
    cV
    cW
    cX
    lmodnegadd.v
    lmodnegadd.r
    lmodnegadd.t
    lmodnegadd.k
    lmodvscl
    syl3anc
    wph
    @11
    cB
    cK
    wcel
    cY
    cV
    wcel
    @10
    lmodnegadd.w
    lmodnegadd.b
    lmodnegadd.y
    cB
    c.x
    cR
    cK
    cV
    cW
    cY
    lmodnegadd.v
    lmodnegadd.r
    lmodnegadd.t
    lmodnegadd.k
    lmodvscl
    syl3anc
    cV
    c.pl
    cW
    cN
    @0
    @1
    lmodnegadd.v
    lmodnegadd.p
    lmodnegadd.n
    ablinvadd
    syl3anc
    wph
    @3
    @6
    @4
    @7
    c.pl
    wph
    cV
    cA
    c.x
    cR
    cK
    cI
    cN
    cW
    cX
    lmodnegadd.v
    lmodnegadd.r
    lmodnegadd.t
    lmodnegadd.n
    lmodnegadd.k
    lmodnegadd.i
    lmodnegadd.w
    lmodnegadd.x
    lmodnegadd.a
    lmodvsneg
    wph
    cV
    cB
    c.x
    cR
    cK
    cI
    cN
    cW
    cY
    lmodnegadd.v
    lmodnegadd.r
    lmodnegadd.t
    lmodnegadd.n
    lmodnegadd.k
    lmodnegadd.i
    lmodnegadd.w
    lmodnegadd.y
    lmodnegadd.b
    lmodvsneg
    oveq12d
    eqtrd
end
