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
include "ply1mulr.mm"
include "mdegmulle2.mm"

theorem deg1mulle2
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cY: class Y
  assume deg1addle.y: |- Y = ( Poly1 ` R )
  assume deg1addle.d: |- D = ( deg1 ` R )
  assume deg1addle.r: |- ( ph -> R e. Ring )
  assume deg1mulle2.b: |- B = ( Base ` Y )
  assume deg1mulle2.t: |- .x. = ( .r ` Y )
  assume deg1mulle2.f: |- ( ph -> F e. B )
  assume deg1mulle2.g: |- ( ph -> G e. B )
  assume deg1mulle2.j1: |- ( ph -> J e. NN0 )
  assume deg1mulle2.k1: |- ( ph -> K e. NN0 )
  assume deg1mulle2.j2: |- ( ph -> ( D ` F ) <_ J )
  assume deg1mulle2.k2: |- ( ph -> ( D ` G ) <_ K )


  assert |- ( ph -> ( D ` ( F .x. G ) ) <_ ( J + K ) )

  proof
    wph
    cB
    cD
    cR
    c.x
    cF
    cG
    c1o
    cJ
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
    deg1mulle2.b
    ply1bas
    cR
    @0
    c.x
    cY
    deg1addle.y
    @1
    deg1mulle2.t
    ply1mulr
    deg1mulle2.f
    deg1mulle2.g
    deg1mulle2.j1
    deg1mulle2.k1
    deg1mulle2.j2
    deg1mulle2.k2
    mdegmulle2
end
