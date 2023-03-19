include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cminusg.mm"
include "cplusg.mm"
include "co.mm"
include "cmpt2.mm"
include "csg.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "eleqtrrd.mm"
include "cgrp.mm"
include "simp3.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "oveqrspc2v.mm"
include "syl12anc.mm"
include "grpinvpropd.mm"
include "fveq1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "mpt2eq3dva.mm"
include "eqtr3d.mm"
include "mpt2eq12.mm"
include "grpsubfval.mm"
include "3eqtr4g.mm"

theorem grpsubpropd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  assume grpsubpropd2.1: |- ( ph -> B = ( Base ` G ) )
  assume grpsubpropd2.2: |- ( ph -> B = ( Base ` H ) )
  assume grpsubpropd2.3: |- ( ph -> G e. Grp )
  assume grpsubpropd2.4: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` G ) y ) = ( x ( +g ` H ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint ph x
  disjoint ph y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint G a
  disjoint b x
  disjoint b y
  disjoint G b
  disjoint H a
  disjoint H b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( -g ` G ) = ( -g ` H ) )

  proof
    wph
    va
    vb
    cG
    cbs
    cfv
    #
    @0
    va
    cv
    #
    vb
    cv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    va
    vb
    cH
    cbs
    cfv
    #
    @8
    @1
    @2
    cH
    cminusg
    cfv
    #
    cfv
    #
    cH
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    cG
    csg
    cfv
    #
    cH
    csg
    cfv
    #
    wph
    @7
    va
    vb
    @0
    @0
    @12
    cmpt2
    #
    @13
    wph
    va
    vb
    @0
    @0
    @6
    @12
    wph
    @1
    @0
    wcel
    #
    @2
    @0
    wcel
    #
    w3a
    #
    @6
    @1
    @4
    @11
    co
    #
    @12
    @19
    wph
    @1
    cB
    wcel
    @4
    cB
    wcel
    @6
    @20
    wceq
    wph
    @17
    @18
    simp1
    @19
    @1
    @0
    cB
    wph
    @17
    @18
    simp2
    wph
    @17
    cB
    @0
    wceq
    @18
    grpsubpropd2.1
    3ad2ant1
    #
    eleqtrrd
    @19
    @4
    @0
    cB
    @19
    cG
    cgrp
    wcel
    #
    @18
    @4
    @0
    wcel
    wph
    @17
    @22
    @18
    grpsubpropd2.3
    3ad2ant1
    wph
    @17
    @18
    simp3
    @0
    cG
    @3
    @2
    @0
    eqid
    #
    @3
    eqid
    #
    grpinvcl
    syl2anc
    @21
    eleqtrrd
    wph
    vx
    vy
    cB
    cB
    @5
    @11
    @1
    @4
    grpsubpropd2.4
    oveqrspc2v
    syl12anc
    wph
    @17
    @20
    @12
    wceq
    @18
    wph
    @4
    @10
    @1
    @11
    wph
    @2
    @3
    @9
    wph
    vx
    vy
    cB
    cG
    cH
    grpsubpropd2.1
    grpsubpropd2.2
    grpsubpropd2.4
    grpinvpropd
    fveq1d
    oveq2d
    3ad2ant1
    eqtrd
    mpt2eq3dva
    wph
    @0
    @8
    wceq
    #
    @25
    @16
    @13
    wceq
    wph
    cB
    @0
    @8
    grpsubpropd2.1
    grpsubpropd2.2
    eqtr3d
    #
    @26
    va
    vb
    @0
    @0
    @8
    @8
    @12
    mpt2eq12
    syl2anc
    eqtrd
    va
    vb
    @0
    @5
    cG
    @3
    @14
    @23
    @5
    eqid
    @24
    @14
    eqid
    grpsubfval
    va
    vb
    @8
    @11
    cH
    @9
    @15
    @8
    eqid
    @11
    eqid
    @9
    eqid
    @15
    eqid
    grpsubfval
    3eqtr4g
end
