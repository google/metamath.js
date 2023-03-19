include "cv.mm"
include "csb.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cvv.mm"
include "cmpt.mm"
include "cprds.mm"
include "co.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "eqid.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "elex.mm"
include "syl.mm"
include "ralrimiva.mm"
include "nfel1.mm"
include "weq.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "cxmt.mm"
include "nffv.mm"
include "nfxp.mm"
include "nfres.mm"
include "nfel.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "eleq12d.mm"
include "prdsxmetlem.mm"

theorem prdsxmet
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cE: class E
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  assume prdsdsf.y: |- Y = ( S Xs_ ( x e. I |-> R ) )
  assume prdsdsf.b: |- B = ( Base ` Y )
  assume prdsdsf.v: |- V = ( Base ` R )
  assume prdsdsf.e: |- E = ( ( dist ` R ) |` ( V X. V ) )
  assume prdsdsf.d: |- D = ( dist ` Y )
  assume prdsdsf.s: |- ( ph -> S e. W )
  assume prdsdsf.i: |- ( ph -> I e. X )
  assume prdsdsf.r: |- ( ( ph /\ x e. I ) -> R e. Z )
  assume prdsdsf.m: |- ( ( ph /\ x e. I ) -> E e. ( *Met ` V ) )

  disjoint I x
  disjoint ph x
  disjoint f g
  disjoint f h
  disjoint f y
  disjoint B f
  disjoint g h
  disjoint g y
  disjoint B g
  disjoint h y
  disjoint B h
  disjoint B y
  disjoint f z
  disjoint D f
  disjoint g z
  disjoint D g
  disjoint h z
  disjoint D h
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint E z
  disjoint f x
  disjoint I f
  disjoint g x
  disjoint I g
  disjoint x y
  disjoint x z
  disjoint I y
  disjoint I z
  disjoint V z
  disjoint f ph
  disjoint g ph
  disjoint h x
  disjoint h ph
  disjoint ph y
  disjoint R f
  disjoint R g
  disjoint R y
  disjoint R z
  disjoint S f
  disjoint S g
  disjoint S y
  disjoint Y f
  disjoint Y g
  disjoint Y y
  assert |- ( ph -> D e. ( *Met ` B ) )

  proof
    wph
    vy
    cB
    cD
    vx
    vy
    cv
    #
    cR
    csb
    #
    cS
    @1
    cds
    cfv
    #
    @1
    cbs
    cfv
    #
    @3
    cxp
    #
    cres
    #
    cI
    @3
    cW
    cX
    cY
    cvv
    cY
    cS
    vx
    cI
    cR
    cmpt
    #
    cprds
    co
    cS
    vy
    cI
    @1
    cmpt
    #
    cprds
    co
    prdsdsf.y
    @6
    @7
    cS
    cprds
    vx
    vy
    cI
    cR
    @1
    vy
    cR
    nfcv
    vx
    @0
    cR
    nfcsb1v
    #
    vx
    @0
    cR
    csbeq1a
    #
    cbvmpt
    oveq2i
    eqtri
    prdsdsf.b
    @3
    eqid
    @5
    eqid
    prdsdsf.d
    prdsdsf.s
    prdsdsf.i
    wph
    cR
    cvv
    wcel
    #
    vx
    cI
    wral
    @0
    cI
    wcel
    #
    @1
    cvv
    wcel
    #
    wph
    @10
    vx
    cI
    wph
    vx
    cv
    cI
    wcel
    wa
    cR
    cZ
    wcel
    @10
    prdsdsf.r
    cR
    cZ
    elex
    syl
    ralrimiva
    @10
    @12
    vx
    @0
    cI
    vx
    @1
    cvv
    @8
    nfel1
    vx
    vy
    weq
    #
    cR
    @1
    cvv
    @9
    eleq1d
    rspc
    mpan9
    wph
    cE
    cV
    cxmt
    cfv
    #
    wcel
    #
    vx
    cI
    wral
    @11
    @5
    @3
    cxmt
    cfv
    #
    wcel
    #
    wph
    @15
    vx
    cI
    prdsdsf.m
    ralrimiva
    @15
    @17
    vx
    @0
    cI
    vx
    @5
    @16
    vx
    @2
    @4
    vx
    @1
    cds
    vx
    cds
    nfcv
    @8
    nffv
    vx
    @3
    @3
    vx
    @1
    cbs
    vx
    cbs
    nfcv
    @8
    nffv
    #
    @18
    nfxp
    nfres
    vx
    @3
    cxmt
    vx
    cxmt
    nfcv
    @18
    nffv
    nfel
    @13
    cE
    @5
    @14
    @16
    @13
    cE
    cR
    cds
    cfv
    #
    cV
    cV
    cxp
    #
    cres
    @5
    prdsdsf.e
    @13
    @19
    @2
    @20
    @4
    @13
    cR
    @1
    cds
    @9
    fveq2d
    @13
    cV
    @3
    @13
    cV
    cR
    cbs
    cfv
    @3
    prdsdsf.v
    @13
    cR
    @1
    cbs
    @9
    fveq2d
    syl5eq
    #
    sqxpeqd
    reseq12d
    syl5eq
    @13
    cV
    @3
    cxmt
    @21
    fveq2d
    eleq12d
    rspc
    mpan9
    prdsxmetlem
end
