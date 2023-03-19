include "cngp.mm"
include "wcel.mm"
include "cgrp.mm"
include "cds.mm"
include "cfv.mm"
include "cme.mm"
include "ccom.mm"
include "cr.mm"
include "wf.mm"
include "cvv.mm"
include "wceq.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "reex.mm"
include "fex2.mm"
include "mp3an23.mm"
include "tngds.mm"
include "3syl.mm"
include "nrmmetd.mm"
include "eqeltrrd.mm"
include "wa.mm"
include "wb.mm"
include "eqid.mm"
include "tngngp2.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem tngngpd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  assume tngngp.t: |- T = ( G toNrmGrp N )
  assume tngngp.x: |- X = ( Base ` G )
  assume tngngp.m: |- .- = ( -g ` G )
  assume tngngp.z: |- .0. = ( 0g ` G )
  assume tngngpd.1: |- ( ph -> G e. Grp )
  assume tngngpd.2: |- ( ph -> N : X --> RR )
  assume tngngpd.3: |- ( ( ph /\ x e. X ) -> ( ( N ` x ) = 0 <-> x = .0. ) )
  assume tngngpd.4: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( N ` ( x .- y ) ) <_ ( ( N ` x ) + ( N ` y ) ) )

  disjoint x y
  disjoint .- x
  disjoint .- y
  disjoint N x
  disjoint N y
  disjoint T x
  disjoint T y
  disjoint X x
  disjoint X y
  disjoint ph x
  disjoint ph y
  disjoint .0. x
  disjoint .0. y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint .- a
  disjoint b x
  disjoint b y
  disjoint .- b
  disjoint N a
  disjoint N b
  disjoint T a
  disjoint T b
  disjoint X a
  disjoint X b
  disjoint G a
  disjoint G b
  disjoint .0. a
  disjoint .0. b
  assert |- ( ph -> T e. NrmGrp )

  proof
    wph
    cT
    cngp
    wcel
    #
    cG
    cgrp
    wcel
    #
    cT
    cds
    cfv
    #
    cX
    cme
    cfv
    #
    wcel
    #
    tngngpd.1
    wph
    cN
    c.mi
    ccom
    #
    @2
    @3
    wph
    cX
    cr
    cN
    wf
    #
    cN
    cvv
    wcel
    #
    @5
    @2
    wceq
    tngngpd.2
    @6
    cX
    cvv
    wcel
    cr
    cvv
    wcel
    @7
    cX
    cG
    cbs
    cfv
    cvv
    tngngp.x
    cG
    cbs
    fvex
    eqeltri
    reex
    cX
    cr
    cN
    cvv
    cvv
    fex2
    mp3an23
    cT
    cG
    c.mi
    cN
    cvv
    tngngp.t
    tngngp.m
    tngds
    3syl
    wph
    vx
    vy
    cN
    cG
    c.mi
    cX
    c.0
    tngngp.x
    tngngp.m
    tngngp.z
    tngngpd.1
    tngngpd.2
    tngngpd.3
    tngngpd.4
    nrmmetd
    eqeltrrd
    wph
    @6
    @0
    @1
    @4
    wa
    wb
    tngngpd.2
    @2
    cT
    cG
    cN
    cX
    tngngp.t
    tngngp.x
    @2
    eqid
    tngngp2
    syl
    mpbir2and
end
