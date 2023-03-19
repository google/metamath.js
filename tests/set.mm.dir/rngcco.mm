include "cop.mm"
include "co.mm"
include "cestrc.mm"
include "cfv.mm"
include "cco.mm"
include "ccom.mm"
include "rngccofval.mm"
include "oveqd.mm"
include "cbs.mm"
include "eqid.mm"
include "estrcco.mm"
include "eqtrd.mm"

theorem rngcco
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
  assume rngcco.c: |- C = ( RngCat ` U )
  assume rngcco.u: |- ( ph -> U e. V )
  assume rngcco.o: |- .x. = ( comp ` C )
  assume rngcco.x: |- ( ph -> X e. U )
  assume rngcco.y: |- ( ph -> Y e. U )
  assume rngcco.z: |- ( ph -> Z e. U )
  assume rngcco.f: |- ( ph -> F : ( Base ` X ) --> ( Base ` Y ) )
  assume rngcco.g: |- ( ph -> G : ( Base ` Y ) --> ( Base ` Z ) )


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
    rngcco.c
    rngcco.u
    rngcco.o
    rngccofval
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
    rngcco.u
    @3
    eqid
    rngcco.x
    rngcco.y
    rngcco.z
    @5
    eqid
    @6
    eqid
    @7
    eqid
    rngcco.f
    rngcco.g
    estrcco
    eqtrd
end
