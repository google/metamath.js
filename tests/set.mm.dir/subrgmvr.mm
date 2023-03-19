include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "wceq.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "cmvr.mm"
include "csubrg.mm"
include "eqid.mm"
include "subrg1.mm"
include "syl.mm"
include "subrg0.mm"
include "ifeq12d.mm"
include "mpteq2dv.mm"
include "crg.mm"
include "subrgrcl.mm"
include "mvrfval.mm"
include "cvv.mm"
include "cress.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "3eqtr4d.mm"

theorem subrgmvr
  let wph: wff ph
  let cR: class R
  let cT: class T
  let cH: class H
  let cI: class I
  let cV: class V
  let cW: class W
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vz: setvar z
  assume subrgmvr.v: |- V = ( I mVar R )
  assume subrgmvr.i: |- ( ph -> I e. W )
  assume subrgmvr.r: |- ( ph -> T e. ( SubRing ` R ) )
  assume subrgmvr.h: |- H = ( R |`s T )


  assert |- ( ph -> V = ( I mVar H ) )

  proof
    wph
    vx
    cI
    vy
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    crab
    #
    vy
    cv
    vz
    cI
    vz
    cv
    vx
    cv
    wceq
    c1
    cc0
    cif
    cmpt
    wceq
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cmpt
    vx
    cI
    vy
    @0
    @1
    cH
    cur
    cfv
    #
    cH
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cmpt
    cV
    cI
    cH
    cmvr
    co
    #
    wph
    vx
    cI
    @5
    @9
    wph
    vy
    @0
    @4
    @8
    wph
    @1
    @2
    @6
    @3
    @7
    wph
    cT
    cR
    csubrg
    cfv
    wcel
    #
    @2
    @6
    wceq
    subrgmvr.r
    cT
    cR
    cH
    @2
    subrgmvr.h
    @2
    eqid
    #
    subrg1
    syl
    wph
    @11
    @3
    @7
    wceq
    subrgmvr.r
    cT
    cR
    cH
    @3
    subrgmvr.h
    @3
    eqid
    #
    subrg0
    syl
    ifeq12d
    mpteq2dv
    mpteq2dv
    wph
    vx
    vz
    @0
    cR
    @2
    vy
    vf
    cI
    cV
    cW
    crg
    @3
    subrgmvr.v
    @0
    eqid
    #
    @13
    @12
    subrgmvr.i
    wph
    @11
    cR
    crg
    wcel
    subrgmvr.r
    cT
    cR
    subrgrcl
    syl
    mvrfval
    wph
    vx
    vz
    @0
    cH
    @6
    vy
    vf
    cI
    @10
    cW
    cvv
    @7
    @10
    eqid
    @14
    @7
    eqid
    @6
    eqid
    subrgmvr.i
    cH
    cvv
    wcel
    wph
    cH
    cR
    cT
    cress
    co
    cvv
    subrgmvr.h
    cR
    cT
    cress
    ovex
    eqeltri
    a1i
    mvrfval
    3eqtr4d
end
