include "cop.mm"
include "co.mm"
include "cestrc.mm"
include "cfv.mm"
include "cco.mm"
include "ccom.mm"
include "ringccofval.mm"
include "oveqd.mm"
include "cbs.mm"
include "eqid.mm"
include "estrcco.mm"
include "eqtrd.mm"

theorem ringcco
  let wph: wff ph
  let cC: class C
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume ringcco.c: |- C = ( RingCat ` U )
  assume ringcco.u: |- ( ph -> U e. V )
  assume ringcco.o: |- .x. = ( comp ` C )
  assume ringcco.x: |- ( ph -> X e. U )
  assume ringcco.y: |- ( ph -> Y e. U )
  assume ringcco.z: |- ( ph -> Z e. U )
  assume ringcco.f: |- ( ph -> F : ( Base ` X ) --> ( Base ` Y ) )
  assume ringcco.g: |- ( ph -> G : ( Base ` Y ) --> ( Base ` Z ) )


  assert |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) = ( G o. F ) )

  proof
    wph
    cG
    cF
    cX
    cY
    cop
    #
    cZ
    c.x
    co
    #
    co
    cG
    cF
    @0
    cZ
    cU
    cestrc
    cfv
    #
    cco
    cfv
    #
    co
    #
    co
    cG
    cF
    ccom
    wph
    @1
    @4
    cG
    cF
    wph
    c.x
    @3
    @0
    cZ
    wph
    cC
    c.x
    cU
    cV
    ringcco.c
    ringcco.u
    ringcco.o
    ringccofval
    oveqd
    oveqd
    wph
    cX
    cbs
    cfv
    #
    cY
    cbs
    cfv
    #
    @2
    cZ
    cbs
    cfv
    #
    @3
    cU
    cF
    cG
    cV
    cX
    cY
    cZ
    @2
    eqid
    ringcco.u
    @3
    eqid
    ringcco.x
    ringcco.y
    ringcco.z
    @5
    eqid
    @6
    eqid
    @7
    eqid
    ringcco.f
    ringcco.g
    estrcco
    eqtrd
end
