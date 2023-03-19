include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "cmpt.mm"
include "c0g.mm"
include "csupp.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmdg.mm"
include "mplbaspropd.mm"
include "grpidpropd.mm"
include "oveq2d.mm"
include "imaeq2d.mm"
include "supeq1d.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "mdegfval.mm"
include "3eqtr4g.mm"

theorem mdegpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let vc: setvar c
  let va: setvar a
  let vb: setvar b
  assume mdegpropd.b1: |- ( ph -> B = ( Base ` R ) )
  assume mdegpropd.b2: |- ( ph -> B = ( Base ` S ) )
  assume mdegpropd.p: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` R ) y ) = ( x ( +g ` S ) y ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint c ph
  disjoint I a
  disjoint I b
  disjoint a b
  disjoint I c
  disjoint R b
  disjoint R c
  disjoint b c
  disjoint S b
  disjoint S c
  assert |- ( ph -> ( I mDeg R ) = ( I mDeg S ) )

  proof
    wph
    vc
    cI
    cR
    cmpl
    co
    #
    cbs
    cfv
    #
    vb
    va
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    va
    cn0
    cI
    cmap
    co
    crab
    #
    ccnfld
    vb
    cv
    cgsu
    co
    cmpt
    #
    vc
    cv
    #
    cR
    c0g
    cfv
    #
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    #
    cmpt
    vc
    cI
    cS
    cmpl
    co
    #
    cbs
    cfv
    #
    @3
    @4
    cS
    c0g
    cfv
    #
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    #
    cmpt
    cI
    cR
    cmdg
    co
    #
    cI
    cS
    cmdg
    co
    #
    wph
    vc
    @1
    @8
    @10
    @14
    wph
    vx
    vy
    cB
    cR
    cS
    cI
    mdegpropd.b1
    mdegpropd.b2
    mdegpropd.p
    mplbaspropd
    wph
    cxr
    @7
    @13
    clt
    wph
    @6
    @12
    @3
    wph
    @5
    @11
    @4
    csupp
    wph
    vx
    vy
    cB
    cR
    cS
    mdegpropd.b1
    mdegpropd.b2
    mdegpropd.p
    grpidpropd
    oveq2d
    imaeq2d
    supeq1d
    mpteq12dv
    @2
    @1
    @15
    @0
    cR
    vc
    vb
    va
    @3
    cI
    @5
    @15
    eqid
    @0
    eqid
    @1
    eqid
    @5
    eqid
    @2
    eqid
    #
    @3
    eqid
    #
    mdegfval
    @2
    @10
    @16
    @9
    cS
    vc
    vb
    va
    @3
    cI
    @11
    @16
    eqid
    @9
    eqid
    @10
    eqid
    @11
    eqid
    @17
    @18
    mdegfval
    3eqtr4g
end
