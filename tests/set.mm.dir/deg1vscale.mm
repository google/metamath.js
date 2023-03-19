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
include "mdegvscale.mm"

theorem deg1vscale
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cY: class Y
  assume deg1addle.y: |- Y = ( Poly1 ` R )
  assume deg1addle.d: |- D = ( deg1 ` R )
  assume deg1addle.r: |- ( ph -> R e. Ring )
  assume deg1vscale.b: |- B = ( Base ` Y )
  assume deg1vscale.k: |- K = ( Base ` R )
  assume deg1vscale.p: |- .x. = ( .s ` Y )
  assume deg1vscale.f: |- ( ph -> F e. K )
  assume deg1vscale.g: |- ( ph -> G e. B )


  assert |- ( ph -> ( D ` ( F .x. G ) ) <_ ( D ` G ) )

  proof
    wph
    cB
    cD
    cR
    c.x
    cF
    cG
    c1o
    cK
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
    deg1vscale.b
    ply1bas
    deg1vscale.k
    cR
    @0
    c.x
    cY
    deg1addle.y
    @1
    deg1vscale.p
    ply1vsca
    deg1vscale.f
    deg1vscale.g
    mdegvscale
end
