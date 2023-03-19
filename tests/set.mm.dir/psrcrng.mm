include "crg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccmn.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "psrring.mm"
include "cbs.mm"
include "cmulr.mm"
include "wceq.mm"
include "eqid.mm"
include "mgpbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "mgpplusg.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "cv.mm"
include "w3a.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "psrcom.mm"
include "iscmnd.mm"
include "iscrng.mm"
include "sylanbrc.mm"

theorem psrcrng
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume psrcnrg.s: |- S = ( I mPwSer R )
  assume psrcnrg.i: |- ( ph -> I e. V )
  assume psrcnrg.r: |- ( ph -> R e. CRing )


  assert |- ( ph -> S e. CRing )

  proof
    wph
    cS
    crg
    wcel
    #
    cS
    cmgp
    cfv
    #
    ccmn
    wcel
    cS
    ccrg
    wcel
    wph
    cR
    cS
    cI
    cV
    psrcnrg.s
    psrcnrg.i
    wph
    cR
    ccrg
    wcel
    #
    cR
    crg
    wcel
    #
    psrcnrg.r
    cR
    crngring
    syl
    #
    psrring
    #
    wph
    vx
    vy
    cS
    cbs
    cfv
    #
    cS
    cmulr
    cfv
    #
    @1
    @6
    @1
    cbs
    cfv
    wceq
    wph
    @6
    cS
    @1
    @1
    eqid
    #
    @6
    eqid
    #
    mgpbas
    a1i
    @7
    @1
    cplusg
    cfv
    wceq
    wph
    cS
    @7
    @1
    @8
    @7
    eqid
    #
    mgpplusg
    a1i
    wph
    @0
    @1
    cmnd
    wcel
    @5
    cS
    @1
    @8
    ringmgp
    syl
    wph
    vx
    cv
    #
    @6
    wcel
    #
    vy
    cv
    #
    @6
    wcel
    #
    w3a
    @6
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
    cR
    cS
    @7
    vf
    cI
    cV
    @11
    @13
    psrcnrg.s
    wph
    @12
    cI
    cV
    wcel
    @14
    psrcnrg.i
    3ad2ant1
    wph
    @12
    @3
    @14
    @4
    3ad2ant1
    @15
    eqid
    @10
    @9
    wph
    @12
    @14
    simp2
    wph
    @12
    @14
    simp3
    wph
    @12
    @2
    @14
    psrcnrg.r
    3ad2ant1
    psrcom
    iscmnd
    cS
    @1
    @8
    iscrng
    sylanbrc
end
