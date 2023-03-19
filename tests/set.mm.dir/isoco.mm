include "cop.mm"
include "co.mm"
include "cinv.mm"
include "cfv.mm"
include "eqid.mm"
include "invco.mm"
include "inviso1.mm"

theorem isoco
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume isoco.b: |- B = ( Base ` C )
  assume isoco.o: |- .x. = ( comp ` C )
  assume isoco.n: |- I = ( Iso ` C )
  assume isoco.c: |- ( ph -> C e. Cat )
  assume isoco.x: |- ( ph -> X e. B )
  assume isoco.y: |- ( ph -> Y e. B )
  assume isoco.z: |- ( ph -> Z e. B )
  assume isoco.f: |- ( ph -> F e. ( X I Y ) )
  assume isoco.g: |- ( ph -> G e. ( Y I Z ) )


  assert |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) e. ( X I Z ) )

  proof
    wph
    cB
    cC
    cG
    cF
    cX
    cY
    cop
    cZ
    c.x
    co
    co
    cF
    cX
    cY
    cC
    cinv
    cfv
    #
    co
    cfv
    cG
    cY
    cZ
    @0
    co
    cfv
    cZ
    cY
    cop
    cX
    c.x
    co
    co
    cI
    @0
    cX
    cZ
    isoco.b
    @0
    eqid
    #
    isoco.c
    isoco.x
    isoco.z
    isoco.n
    wph
    cB
    cC
    c.x
    cF
    cG
    cI
    @0
    cX
    cY
    cZ
    isoco.b
    @1
    isoco.c
    isoco.x
    isoco.y
    isoco.n
    isoco.f
    isoco.o
    isoco.z
    isoco.g
    invco
    inviso1
end
