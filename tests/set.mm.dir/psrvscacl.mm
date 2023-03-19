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
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cfv.mm"
include "cof.mm"
include "wf.mm"
include "cvv.mm"
include "crg.mm"
include "wa.mm"
include "eqid.mm"
include "ringcl.mm"
include "3expb.mm"
include "sylan.mm"
include "fconst6g.mm"
include "syl.mm"
include "psrelbas.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "inidm.mm"
include "off.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "sylibr.mm"
include "psrvsca.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "elbasov.mm"
include "simpld.mm"
include "psrbas.mm"
include "3eltr4d.mm"

theorem psrvscacl
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cI: class I
  let cK: class K
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume psrvscacl.s: |- S = ( I mPwSer R )
  assume psrvscacl.n: |- .x. = ( .s ` S )
  assume psrvscacl.k: |- K = ( Base ` R )
  assume psrvscacl.b: |- B = ( Base ` S )
  assume psrvscacl.r: |- ( ph -> R e. Ring )
  assume psrvscacl.x: |- ( ph -> X e. K )
  assume psrvscacl.y: |- ( ph -> F e. B )


  assert |- ( ph -> ( X .x. F ) e. B )

  proof
    wph
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vf
    cn0
    cI
    cmap
    co
    #
    crab
    #
    cX
    csn
    cxp
    #
    cF
    cR
    cmulr
    cfv
    #
    cof
    co
    #
    cK
    @2
    cmap
    co
    #
    cX
    cF
    c.x
    co
    cB
    wph
    @2
    cK
    @5
    wf
    @5
    @6
    wcel
    wph
    vx
    vy
    @2
    @2
    @2
    @4
    cK
    cK
    cK
    @3
    cF
    cvv
    cvv
    wph
    cR
    crg
    wcel
    #
    vx
    cv
    #
    cK
    wcel
    #
    vy
    cv
    #
    cK
    wcel
    #
    wa
    @8
    @10
    @4
    co
    cK
    wcel
    #
    psrvscacl.r
    @7
    @9
    @11
    @12
    cK
    cR
    @4
    @8
    @10
    psrvscacl.k
    @4
    eqid
    #
    ringcl
    3expb
    sylan
    wph
    cX
    cK
    wcel
    @2
    cK
    @3
    wf
    psrvscacl.x
    @2
    cX
    cK
    fconst6g
    syl
    wph
    cB
    @2
    cR
    cS
    vf
    cI
    cK
    cF
    psrvscacl.s
    psrvscacl.k
    @2
    eqid
    #
    psrvscacl.b
    psrvscacl.y
    psrelbas
    @2
    cvv
    wcel
    wph
    @0
    vf
    @1
    cn0
    cI
    cmap
    ovex
    rabex
    #
    a1i
    #
    @16
    @2
    inidm
    off
    cK
    @2
    @5
    cK
    cR
    cbs
    cfv
    cvv
    psrvscacl.k
    cR
    cbs
    fvex
    eqeltri
    @15
    elmap
    sylibr
    wph
    cB
    @2
    cR
    cS
    c.x
    @4
    vf
    cF
    cI
    cK
    cX
    psrvscacl.s
    psrvscacl.n
    psrvscacl.k
    psrvscacl.b
    @13
    @14
    psrvscacl.x
    psrvscacl.y
    psrvsca
    wph
    cB
    @2
    cR
    cS
    vf
    cI
    cK
    cvv
    psrvscacl.s
    psrvscacl.k
    @14
    psrvscacl.b
    wph
    cI
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wph
    cF
    cB
    wcel
    @17
    @18
    wa
    psrvscacl.y
    cF
    cB
    cS
    cmps
    cI
    cR
    reldmpsr
    psrvscacl.s
    psrvscacl.b
    elbasov
    syl
    simpld
    psrbas
    3eltr4d
end
