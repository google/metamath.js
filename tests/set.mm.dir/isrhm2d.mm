include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crh.mm"
include "jca.mm"
include "cmnd.mm"
include "cbs.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "eqid.mm"
include "ringmgp.mm"
include "syl.mm"
include "ghmf.mm"
include "ralrimivva.mm"
include "ringidval.mm"
include "fveq2i.mm"
include "3eqtr3g.mm"
include "3jca.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "ismhm.mm"
include "sylanbrc.mm"
include "isrhm.mm"

theorem isrhm2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let c.1: class .1.
  let cF: class F
  let cN: class N
  let cC: class C
  let c.pl: class .+
  let c.pd: class .+^
  assume isrhmd.b: |- B = ( Base ` R )
  assume isrhmd.o: |- .1. = ( 1r ` R )
  assume isrhmd.n: |- N = ( 1r ` S )
  assume isrhmd.t: |- .x. = ( .r ` R )
  assume isrhmd.u: |- .X. = ( .r ` S )
  assume isrhmd.r: |- ( ph -> R e. Ring )
  assume isrhmd.s: |- ( ph -> S e. Ring )
  assume isrhmd.ho: |- ( ph -> ( F ` .1. ) = N )
  assume isrhmd.ht: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( F ` ( x .x. y ) ) = ( ( F ` x ) .X. ( F ` y ) ) )
  assume isrhm2d.f: |- ( ph -> F e. ( R GrpHom S ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint C x
  disjoint C y
  disjoint .+ x
  disjoint .+ y
  disjoint .+^ x
  disjoint .+^ y
  assert |- ( ph -> F e. ( R RingHom S ) )

  proof
    wph
    cR
    crg
    wcel
    #
    cS
    crg
    wcel
    #
    wa
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    cF
    cR
    cmgp
    cfv
    #
    cS
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    wa
    cF
    cR
    cS
    crh
    co
    wcel
    wph
    @0
    @1
    isrhmd.r
    isrhmd.s
    jca
    wph
    @2
    @5
    isrhm2d.f
    wph
    @3
    cmnd
    wcel
    #
    @4
    cmnd
    wcel
    #
    wa
    cB
    cS
    cbs
    cfv
    #
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    cF
    cfv
    @10
    cF
    cfv
    @11
    cF
    cfv
    c.xp
    co
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @3
    c0g
    cfv
    #
    cF
    cfv
    #
    @4
    c0g
    cfv
    #
    wceq
    #
    w3a
    @5
    wph
    @6
    @7
    wph
    @0
    @6
    isrhmd.r
    cR
    @3
    @3
    eqid
    #
    ringmgp
    syl
    wph
    @1
    @7
    isrhmd.s
    cS
    @4
    @4
    eqid
    #
    ringmgp
    syl
    jca
    wph
    @9
    @13
    @17
    wph
    @2
    @9
    isrhm2d.f
    cR
    cS
    cF
    cB
    @8
    isrhmd.b
    @8
    eqid
    #
    ghmf
    syl
    wph
    @12
    vx
    vy
    cB
    cB
    isrhmd.ht
    ralrimivva
    wph
    c.1
    cF
    cfv
    cN
    @15
    @16
    isrhmd.ho
    c.1
    @14
    cF
    cR
    c.1
    @3
    @18
    isrhmd.o
    ringidval
    fveq2i
    cS
    cN
    @4
    @19
    isrhmd.n
    ringidval
    3eqtr3g
    3jca
    vx
    vy
    cB
    @8
    c.x
    c.xp
    @3
    @4
    cF
    @16
    @14
    cB
    cR
    @3
    @18
    isrhmd.b
    mgpbas
    @8
    cS
    @4
    @19
    @20
    mgpbas
    cR
    c.x
    @3
    @18
    isrhmd.t
    mgpplusg
    cS
    c.xp
    @4
    @19
    isrhmd.u
    mgpplusg
    @14
    eqid
    @16
    eqid
    ismhm
    sylanbrc
    jca
    cR
    cS
    cF
    @3
    @4
    @18
    @19
    isrhm
    sylanbrc
end
