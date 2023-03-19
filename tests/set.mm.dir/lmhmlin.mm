include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cghm.mm"
include "csca.mm"
include "clmod.mm"
include "w3a.mm"
include "eqid.mm"
include "islmhm.mm"
include "simprbi.mm"
include "simp3d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem lmhmlin
  let cB: class B
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cE: class E
  let cF: class F
  let cK: class K
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume lmhmlin.k: |- K = ( Scalar ` S )
  assume lmhmlin.b: |- B = ( Base ` K )
  assume lmhmlin.e: |- E = ( Base ` S )
  assume lmhmlin.m: |- .x. = ( .s ` S )
  assume lmhmlin.n: |- .X. = ( .s ` T )


  assert |- ( ( F e. ( S LMHom T ) /\ X e. B /\ Y e. E ) -> ( F ` ( X .x. Y ) ) = ( X .X. ( F ` Y ) ) )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cE
    wcel
    #
    cX
    cY
    c.x
    co
    #
    cF
    cfv
    #
    cX
    cY
    cF
    cfv
    #
    c.xp
    co
    #
    wceq
    #
    @0
    va
    cv
    #
    vb
    cv
    #
    c.x
    co
    #
    cF
    cfv
    #
    @8
    @9
    cF
    cfv
    #
    c.xp
    co
    #
    wceq
    #
    vb
    cE
    wral
    va
    cB
    wral
    #
    @1
    @2
    wa
    @7
    @0
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cT
    csca
    cfv
    #
    cK
    wceq
    #
    @15
    @0
    cS
    clmod
    wcel
    cT
    clmod
    wcel
    wa
    @16
    @18
    @15
    w3a
    va
    vb
    cB
    cS
    cT
    c.x
    c.xp
    cE
    cF
    cK
    @17
    lmhmlin.k
    @17
    eqid
    lmhmlin.b
    lmhmlin.e
    lmhmlin.m
    lmhmlin.n
    islmhm
    simprbi
    simp3d
    @14
    @7
    cX
    @9
    c.x
    co
    #
    cF
    cfv
    #
    cX
    @12
    c.xp
    co
    #
    wceq
    va
    vb
    cX
    cY
    cB
    cE
    @8
    cX
    wceq
    #
    @11
    @20
    @13
    @21
    @22
    @10
    @19
    cF
    @8
    cX
    @9
    c.x
    oveq1
    fveq2d
    @8
    cX
    @12
    c.xp
    oveq1
    eqeq12d
    @9
    cY
    wceq
    #
    @20
    @4
    @21
    @6
    @23
    @19
    @3
    cF
    @9
    cY
    cX
    c.x
    oveq2
    fveq2d
    @23
    @12
    @5
    cX
    c.xp
    @9
    cY
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    syl5com
    3impib
end
