include "wf.mm"
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
include "wa.mm"
include "cbs.mm"
include "crg.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "ad2antrr.mm"
include "fmptd.mm"
include "fvex.mm"
include "ovex.mm"
include "rabex.mm"
include "elmap.mm"
include "sylibr.mm"
include "psrbas.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "mvrfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem mvrf
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mvrf.s: |- S = ( I mPwSer R )
  assume mvrf.v: |- V = ( I mVar R )
  assume mvrf.b: |- B = ( Base ` S )
  assume mvrf.i: |- ( ph -> I e. W )
  assume mvrf.r: |- ( ph -> R e. Ring )


  assert |- ( ph -> V : I --> B )

  proof
    wph
    cI
    cB
    cV
    wf
    cI
    cB
    vx
    cI
    vf
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vh
    cn0
    cI
    cmap
    co
    #
    crab
    #
    vf
    cv
    #
    vy
    cI
    vy
    cv
    vx
    cv
    #
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
    #
    wf
    wph
    vx
    cI
    @9
    cB
    @10
    wph
    @4
    cI
    wcel
    #
    wa
    #
    @9
    cR
    cbs
    cfv
    #
    @2
    cmap
    co
    #
    cB
    @12
    @2
    @13
    @9
    wf
    @9
    @14
    wcel
    @12
    vf
    @2
    @8
    @13
    @9
    wph
    @8
    @13
    wcel
    @11
    @3
    @2
    wcel
    wph
    @5
    @6
    @7
    @13
    wph
    cR
    crg
    wcel
    #
    @6
    @13
    wcel
    mvrf.r
    @13
    cR
    @6
    @13
    eqid
    #
    @6
    eqid
    #
    ringidcl
    syl
    wph
    @15
    @7
    @13
    wcel
    mvrf.r
    @13
    cR
    @7
    @16
    @7
    eqid
    #
    ring0cl
    syl
    ifcld
    ad2antrr
    @9
    eqid
    fmptd
    @13
    @2
    @9
    cR
    cbs
    fvex
    @0
    vh
    @1
    cn0
    cI
    cmap
    ovex
    rabex
    elmap
    sylibr
    wph
    cB
    @14
    wceq
    @11
    wph
    cB
    @2
    cR
    cS
    vh
    cI
    @13
    cW
    mvrf.s
    @16
    @2
    eqid
    #
    mvrf.b
    mvrf.i
    psrbas
    adantr
    eleqtrrd
    @10
    eqid
    fmptd
    wph
    cI
    cB
    cV
    @10
    wph
    vx
    vy
    @2
    cR
    @6
    vf
    vh
    cI
    cV
    cW
    crg
    @7
    mvrf.v
    @19
    @18
    @17
    mvrf.i
    mvrf.r
    mvrfval
    feq1d
    mpbird
end
