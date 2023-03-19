include "co.mm"
include "cfv.mm"
include "wbr.mm"
include "invisoinvl.mm"
include "invsym.mm"
include "mpbird.mm"

theorem invisoinvr
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  assume invisoinv.b: |- B = ( Base ` C )
  assume invisoinv.i: |- I = ( Iso ` C )
  assume invisoinv.n: |- N = ( Inv ` C )
  assume invisoinv.c: |- ( ph -> C e. Cat )
  assume invisoinv.x: |- ( ph -> X e. B )
  assume invisoinv.y: |- ( ph -> Y e. B )
  assume invisoinv.f: |- ( ph -> F e. ( X I Y ) )


  assert |- ( ph -> F ( X N Y ) ( ( X N Y ) ` F ) )

  proof
    wph
    cF
    cF
    cX
    cY
    cN
    co
    #
    cfv
    #
    @0
    wbr
    @1
    cF
    cY
    cX
    cN
    co
    wbr
    wph
    cB
    cC
    cF
    cI
    cN
    cX
    cY
    invisoinv.b
    invisoinv.i
    invisoinv.n
    invisoinv.c
    invisoinv.x
    invisoinv.y
    invisoinv.f
    invisoinvl
    wph
    cB
    cC
    cF
    @1
    cN
    cX
    cY
    invisoinv.b
    invisoinv.n
    invisoinv.c
    invisoinv.x
    invisoinv.y
    invsym
    mpbird
end
