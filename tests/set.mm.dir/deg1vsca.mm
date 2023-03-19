include "c1o.mm"
include "con0.mm"
include "cmpl.mm"
include "co.mm"
include "eqid.mm"
include "deg1fval.mm"
include "wcel.mm"
include "1on.mm"
include "a1i.mm"
include "cps1.mm"
include "cfv.mm"
include "ply1bas.mm"
include "ply1vsca.mm"
include "mdegvsca.mm"

theorem deg1vsca
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cG: class G
  let cY: class Y
  assume deg1addle.y: |- Y = ( Poly1 ` R )
  assume deg1addle.d: |- D = ( deg1 ` R )
  assume deg1addle.r: |- ( ph -> R e. Ring )
  assume deg1vsca.b: |- B = ( Base ` Y )
  assume deg1vsca.e: |- E = ( RLReg ` R )
  assume deg1vsca.p: |- .x. = ( .s ` Y )
  assume deg1vsca.f: |- ( ph -> F e. E )
  assume deg1vsca.g: |- ( ph -> G e. B )


  assert |- ( ph -> ( D ` ( F .x. G ) ) = ( D ` G ) )

  proof
    wph
    cB
    cD
    cR
    c.x
    cE
    cF
    cG
    c1o
    con0
    c1o
    cR
    cmpl
    co
    #
    @0
    eqid
    #
    cD
    cR
    deg1addle.d
    deg1fval
    c1o
    con0
    wcel
    wph
    1on
    a1i
    deg1addle.r
    cY
    cR
    cR
    cps1
    cfv
    #
    cB
    deg1addle.y
    @2
    eqid
    deg1vsca.b
    ply1bas
    deg1vsca.e
    cR
    @0
    c.x
    cY
    deg1addle.y
    @1
    deg1vsca.p
    ply1vsca
    deg1vsca.f
    deg1vsca.g
    mdegvsca
end
