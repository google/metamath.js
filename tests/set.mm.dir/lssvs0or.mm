include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "wne.mm"
include "cinvr.mm"
include "cfv.mm"
include "cmulr.mm"
include "cur.mm"
include "cdr.mm"
include "clvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "eqid.mm"
include "drnginvrl.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "clmod.mm"
include "lveclmod.mm"
include "drnginvrcl.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "3eqtr3rd.mm"
include "simplr.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "eqeltrd.mm"
include "ex.mm"
include "necon1bd.mm"
include "orrd.mm"
include "orcomd.mm"
include "oveq1.mm"
include "adantl.mm"
include "c0g.mm"
include "lmod0vs.mm"
include "lss0cl.mm"
include "adantr.mm"
include "jaodan.mm"
include "impbida.mm"

theorem lssvs0or
  let wph: wff ph
  let cA: class A
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lssvs0or.v: |- V = ( Base ` W )
  assume lssvs0or.t: |- .x. = ( .s ` W )
  assume lssvs0or.f: |- F = ( Scalar ` W )
  assume lssvs0or.k: |- K = ( Base ` F )
  assume lssvs0or.o: |- .0. = ( 0g ` F )
  assume lssvs0or.s: |- S = ( LSubSp ` W )
  assume lssvs0or.w: |- ( ph -> W e. LVec )
  assume lssvs0or.u: |- ( ph -> U e. S )
  assume lssvs0or.x: |- ( ph -> X e. V )
  assume lssvs0or.a: |- ( ph -> A e. K )


  assert |- ( ph -> ( ( A .x. X ) e. U <-> ( A = .0. \/ X e. U ) ) )

  proof
    wph
    cA
    cX
    c.x
    co
    #
    cU
    wcel
    #
    cA
    c.0
    wceq
    #
    cX
    cU
    wcel
    #
    wo
    wph
    @1
    wa
    #
    @3
    @2
    @4
    @3
    @2
    @4
    @3
    cA
    c.0
    @4
    cA
    c.0
    wne
    #
    @3
    @4
    @5
    wa
    #
    cX
    cA
    cF
    cinvr
    cfv
    #
    cfv
    #
    @0
    c.x
    co
    #
    cU
    @6
    @8
    cA
    cF
    cmulr
    cfv
    #
    co
    #
    cX
    c.x
    co
    #
    cF
    cur
    cfv
    #
    cX
    c.x
    co
    #
    @9
    cX
    @6
    @11
    @13
    cX
    c.x
    @6
    cF
    cdr
    wcel
    #
    cA
    cK
    wcel
    #
    @5
    @11
    @13
    wceq
    wph
    @15
    @1
    @5
    wph
    cW
    clvec
    wcel
    #
    @15
    lssvs0or.w
    cF
    cW
    lssvs0or.f
    lvecdrng
    syl
    ad2antrr
    #
    wph
    @16
    @1
    @5
    lssvs0or.a
    ad2antrr
    #
    @4
    @5
    simpr
    #
    cK
    cF
    @10
    @13
    @7
    cA
    c.0
    lssvs0or.k
    lssvs0or.o
    @10
    eqid
    #
    @13
    eqid
    #
    @7
    eqid
    #
    drnginvrl
    syl3anc
    oveq1d
    @6
    cW
    clmod
    wcel
    #
    @8
    cK
    wcel
    #
    @16
    cX
    cV
    wcel
    #
    @12
    @9
    wceq
    wph
    @24
    @1
    @5
    wph
    @17
    @24
    lssvs0or.w
    cW
    lveclmod
    syl
    #
    ad2antrr
    #
    @6
    @15
    @16
    @5
    @25
    @18
    @19
    @20
    cK
    cF
    @7
    cA
    c.0
    lssvs0or.k
    lssvs0or.o
    @23
    drnginvrcl
    syl3anc
    #
    @19
    wph
    @26
    @1
    @5
    lssvs0or.x
    ad2antrr
    #
    @8
    cA
    c.x
    @10
    cF
    cK
    cV
    cW
    cX
    lssvs0or.v
    lssvs0or.f
    lssvs0or.t
    lssvs0or.k
    @21
    lmodvsass
    syl13anc
    @6
    @24
    @26
    @14
    cX
    wceq
    @28
    @30
    c.x
    @13
    cF
    cV
    cW
    cX
    lssvs0or.v
    lssvs0or.f
    lssvs0or.t
    @22
    lmodvs1
    syl2anc
    3eqtr3rd
    @6
    @24
    cU
    cS
    wcel
    #
    @25
    @1
    @9
    cU
    wcel
    @28
    wph
    @31
    @1
    @5
    lssvs0or.u
    ad2antrr
    @29
    wph
    @1
    @5
    simplr
    cK
    cS
    c.x
    cU
    cF
    cW
    @8
    @0
    lssvs0or.f
    lssvs0or.t
    lssvs0or.k
    lssvs0or.s
    lssvscl
    syl22anc
    eqeltrd
    ex
    necon1bd
    orrd
    orcomd
    wph
    @2
    @1
    @3
    wph
    @2
    wa
    @0
    c.0
    cX
    c.x
    co
    #
    cU
    @2
    @0
    @32
    wceq
    wph
    cA
    c.0
    cX
    c.x
    oveq1
    adantl
    wph
    @32
    cU
    wcel
    @2
    wph
    @32
    cW
    c0g
    cfv
    #
    cU
    wph
    @24
    @26
    @32
    @33
    wceq
    @27
    lssvs0or.x
    c.x
    cF
    c.0
    cV
    cW
    cX
    @33
    lssvs0or.v
    lssvs0or.f
    lssvs0or.t
    lssvs0or.o
    @33
    eqid
    #
    lmod0vs
    syl2anc
    wph
    @24
    @31
    @33
    cU
    wcel
    @27
    lssvs0or.u
    cS
    cU
    cW
    @33
    @34
    lssvs0or.s
    lss0cl
    syl2anc
    eqeltrd
    adantr
    eqeltrd
    wph
    @3
    wa
    @24
    @31
    @16
    @3
    @1
    wph
    @24
    @3
    @27
    adantr
    wph
    @31
    @3
    lssvs0or.u
    adantr
    wph
    @16
    @3
    lssvs0or.a
    adantr
    wph
    @3
    simpr
    cK
    cS
    c.x
    cU
    cF
    cW
    cA
    cX
    lssvs0or.f
    lssvs0or.t
    lssvs0or.k
    lssvs0or.s
    lssvscl
    syl22anc
    jaodan
    impbida
end
