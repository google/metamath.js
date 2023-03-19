include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "con0.mm"
include "eqid.mm"
include "deg1fval.mm"
include "wcel.mm"
include "1on.mm"
include "a1i.mm"
include "ply1plusg.mm"
include "ply1bascl2.mm"
include "syl.mm"
include "mdegaddle.mm"

theorem deg1addle
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let cF: class F
  let cG: class G
  let cY: class Y
  assume deg1addle.y: |- Y = ( Poly1 ` R )
  assume deg1addle.d: |- D = ( deg1 ` R )
  assume deg1addle.r: |- ( ph -> R e. Ring )
  assume deg1addle.b: |- B = ( Base ` Y )
  assume deg1addle.p: |- .+ = ( +g ` Y )
  assume deg1addle.f: |- ( ph -> F e. B )
  assume deg1addle.g: |- ( ph -> G e. B )


  assert |- ( ph -> ( D ` ( F .+ G ) ) <_ if ( ( D ` F ) <_ ( D ` G ) , ( D ` G ) , ( D ` F ) ) )

  proof
    wph
    c1o
    cR
    cmpl
    co
    #
    cbs
    cfv
    #
    cD
    c.pl
    cR
    cF
    cG
    c1o
    con0
    @0
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
    @1
    eqid
    c.pl
    cR
    @0
    cY
    deg1addle.y
    @2
    deg1addle.p
    ply1plusg
    wph
    cF
    cB
    wcel
    cF
    @1
    wcel
    deg1addle.f
    cB
    cY
    cR
    cF
    deg1addle.y
    deg1addle.b
    ply1bascl2
    syl
    wph
    cG
    cB
    wcel
    cG
    @1
    wcel
    deg1addle.g
    cB
    cY
    cR
    cG
    deg1addle.y
    deg1addle.b
    ply1bascl2
    syl
    mdegaddle
end
