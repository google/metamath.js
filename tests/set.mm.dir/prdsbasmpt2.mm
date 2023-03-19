include "cmpt.mm"
include "wcel.mm"
include "cixp.mm"
include "wral.mm"
include "prdsbas3.mm"
include "eleq2d.mm"
include "wb.mm"
include "mptelixpg.mm"
include "syl.mm"
include "bitrd.mm"

theorem prdsbasmpt2
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let cF: class F
  let cG: class G
  assume prdsbasmpt2.y: |- Y = ( S Xs_ ( x e. I |-> R ) )
  assume prdsbasmpt2.b: |- B = ( Base ` Y )
  assume prdsbasmpt2.s: |- ( ph -> S e. V )
  assume prdsbasmpt2.i: |- ( ph -> I e. W )
  assume prdsbasmpt2.r: |- ( ph -> A. x e. I R e. X )
  assume prdsbasmpt2.k: |- K = ( Base ` R )

  disjoint I x
  disjoint B y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint ph y
  disjoint S y
  disjoint V y
  disjoint I y
  disjoint R y
  disjoint W y
  disjoint Y y
  assert |- ( ph -> ( ( x e. I |-> U ) e. B <-> A. x e. I U e. K ) )

  proof
    wph
    vx
    cI
    cU
    cmpt
    #
    cB
    wcel
    @0
    vx
    cI
    cK
    cixp
    #
    wcel
    #
    cU
    cK
    wcel
    vx
    cI
    wral
    #
    wph
    cB
    @1
    @0
    wph
    vx
    cB
    cR
    cS
    cI
    cK
    cV
    cW
    cX
    cY
    prdsbasmpt2.y
    prdsbasmpt2.b
    prdsbasmpt2.s
    prdsbasmpt2.i
    prdsbasmpt2.r
    prdsbasmpt2.k
    prdsbas3
    eleq2d
    wph
    cI
    cW
    wcel
    @2
    @3
    wb
    prdsbasmpt2.i
    vx
    cI
    cU
    cK
    cW
    mptelixpg
    syl
    bitrd
end
