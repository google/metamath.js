include "co.mm"
include "crn.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cun.mm"
include "coch.mm"
include "cfv.mm"
include "chlt.mm"
include "wss.mm"
include "adantr.mm"
include "lssss.mm"
include "syl.mm"
include "eqid.mm"
include "djhval2.mm"
include "syl3anc.mm"
include "clspn.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lsmsp.mm"
include "fveq2d.mm"
include "unssd.mm"
include "dochocsp.mm"
include "eqtrd.mm"
include "dochoc.mm"
include "sylan.mm"
include "3eqtr2rd.mm"
include "ex.mm"
include "wi.mm"
include "djhcl.mm"
include "syl12anc.mm"
include "eleq1a.mm"
include "impbid.mm"

theorem djhlsmcl
  let wph: wff ph
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume djhlsmcl.h: |- H = ( LHyp ` K )
  assume djhlsmcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhlsmcl.v: |- V = ( Base ` U )
  assume djhlsmcl.s: |- S = ( LSubSp ` U )
  assume djhlsmcl.p: |- .(+) = ( LSSum ` U )
  assume djhlsmcl.i: |- I = ( ( DIsoH ` K ) ` W )
  assume djhlsmcl.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume djhlsmcl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume djhlsmcl.x: |- ( ph -> X e. S )
  assume djhlsmcl.y: |- ( ph -> Y e. S )


  assert |- ( ph -> ( ( X .(+) Y ) e. ran I <-> ( X .(+) Y ) = ( X .\/ Y ) ) )

  proof
    wph
    cX
    cY
    c.po
    co
    #
    cI
    crn
    #
    wcel
    #
    @0
    cX
    cY
    c.or
    co
    #
    wceq
    #
    wph
    @2
    @4
    wph
    @2
    wa
    #
    @3
    cX
    cY
    cun
    #
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    #
    @7
    cfv
    #
    @0
    @7
    cfv
    #
    @7
    cfv
    #
    @0
    @5
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wss
    #
    cY
    cV
    wss
    #
    @3
    @9
    wceq
    wph
    @12
    @2
    djhlsmcl.k
    adantr
    #
    wph
    @13
    @2
    wph
    cX
    cS
    wcel
    #
    @13
    djhlsmcl.x
    cS
    cX
    cV
    cU
    djhlsmcl.v
    djhlsmcl.s
    lssss
    syl
    #
    adantr
    wph
    @14
    @2
    wph
    cY
    cS
    wcel
    #
    @14
    djhlsmcl.y
    cS
    cY
    cV
    cU
    djhlsmcl.v
    djhlsmcl.s
    lssss
    syl
    #
    adantr
    cU
    cH
    c.or
    cK
    @7
    cV
    cW
    cX
    cY
    djhlsmcl.h
    djhlsmcl.u
    djhlsmcl.v
    @7
    eqid
    #
    djhlsmcl.j
    djhval2
    syl3anc
    @5
    @10
    @8
    @7
    @5
    @10
    @6
    cU
    clspn
    cfv
    #
    cfv
    #
    @7
    cfv
    @8
    @5
    @0
    @22
    @7
    @5
    cU
    clmod
    wcel
    #
    @16
    @18
    @0
    @22
    wceq
    wph
    @23
    @2
    wph
    cU
    cH
    cK
    cW
    djhlsmcl.h
    djhlsmcl.u
    djhlsmcl.k
    dvhlmod
    adantr
    wph
    @16
    @2
    djhlsmcl.x
    adantr
    wph
    @18
    @2
    djhlsmcl.y
    adantr
    c.po
    cS
    cX
    cY
    @21
    cU
    djhlsmcl.s
    @21
    eqid
    #
    djhlsmcl.p
    lsmsp
    syl3anc
    fveq2d
    @5
    cU
    cH
    cK
    @21
    @7
    cV
    cW
    @6
    djhlsmcl.h
    djhlsmcl.u
    @20
    djhlsmcl.v
    @24
    @15
    wph
    @6
    cV
    wss
    @2
    wph
    cX
    cY
    cV
    @17
    @19
    unssd
    adantr
    dochocsp
    eqtrd
    fveq2d
    wph
    @12
    @2
    @11
    @0
    wceq
    djhlsmcl.k
    cH
    cI
    cK
    @7
    cW
    @0
    djhlsmcl.h
    djhlsmcl.i
    @20
    dochoc
    sylan
    3eqtr2rd
    ex
    wph
    @3
    @1
    wcel
    #
    @4
    @2
    wi
    wph
    @12
    @13
    @14
    @25
    djhlsmcl.k
    @17
    @19
    cU
    cH
    cI
    c.or
    cK
    cV
    cW
    cX
    cY
    djhlsmcl.h
    djhlsmcl.i
    djhlsmcl.u
    djhlsmcl.v
    djhlsmcl.j
    djhcl
    syl12anc
    @3
    @1
    @0
    eleq1a
    syl
    impbid
end
