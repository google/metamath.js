include "cbs.mm"
include "cfv.mm"
include "cvsca.mm"
include "cmulr.mm"
include "eqidd.mm"
include "ccrg.mm"
include "psrsca.mm"
include "wcel.mm"
include "crg.mm"
include "crngring.mm"
include "syl.mm"
include "psrlmod.mm"
include "psrring.mm"
include "cv.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "adantr.mm"
include "eqid.mm"
include "simpr2.mm"
include "simpr3.mm"
include "simpr1.mm"
include "psrass23.mm"
include "simpld.mm"
include "simprd.mm"
include "isassad.mm"

theorem psrassa
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


  assert |- ( ph -> S e. AssAlg )

  proof
    wph
    vy
    vz
    cR
    cbs
    cfv
    #
    cS
    cvsca
    cfv
    #
    cS
    cmulr
    cfv
    #
    cR
    cS
    cbs
    cfv
    #
    cS
    vx
    wph
    @3
    eqidd
    wph
    cR
    cS
    cI
    cV
    ccrg
    psrcnrg.s
    psrcnrg.i
    psrcnrg.r
    psrsca
    wph
    @0
    eqidd
    wph
    @1
    eqidd
    wph
    @2
    eqidd
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
    psrlmod
    wph
    cR
    cS
    cI
    cV
    psrcnrg.s
    psrcnrg.i
    @6
    psrring
    psrcnrg.r
    wph
    vx
    cv
    #
    @0
    wcel
    #
    vy
    cv
    #
    @3
    wcel
    #
    vz
    cv
    #
    @3
    wcel
    #
    w3a
    #
    wa
    #
    @7
    @9
    @1
    co
    @11
    @2
    co
    @7
    @9
    @11
    @2
    co
    @1
    co
    #
    wceq
    #
    @9
    @7
    @11
    @1
    co
    @2
    co
    @15
    wceq
    #
    @14
    @7
    @3
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
    @1
    @2
    vf
    cI
    @0
    cV
    @9
    @11
    psrcnrg.s
    wph
    cI
    cV
    wcel
    @13
    psrcnrg.i
    adantr
    wph
    @5
    @13
    @6
    adantr
    @18
    eqid
    @2
    eqid
    @3
    eqid
    wph
    @8
    @10
    @12
    simpr2
    wph
    @8
    @10
    @12
    simpr3
    wph
    @4
    @13
    psrcnrg.r
    adantr
    @0
    eqid
    @1
    eqid
    wph
    @8
    @10
    @12
    simpr1
    psrass23
    #
    simpld
    @14
    @16
    @17
    @19
    simprd
    isassad
end
