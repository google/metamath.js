include "co.mm"
include "cfv.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "wa.mm"
include "clsm.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cinvr.mm"
include "csg.mm"
include "clspn.mm"
include "eqid.mm"
include "wcel.mm"
include "adantr.mm"
include "chlt.mm"
include "csn.mm"
include "simpr.mm"
include "lclkrlem2u.mm"
include "sylan2br.mm"
include "lclkrlem2t.mm"
include "simprl.mm"
include "simprr.mm"
include "lclkrlem2w.mm"
include "pm2.61dda.mm"

theorem lclkrlem2x
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lclkrlem2x.l: |- L = ( LKer ` U )
  assume lclkrlem2x.h: |- H = ( LHyp ` K )
  assume lclkrlem2x.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrlem2x.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrlem2x.v: |- V = ( Base ` U )
  assume lclkrlem2x.f: |- F = ( LFnl ` U )
  assume lclkrlem2x.d: |- D = ( LDual ` U )
  assume lclkrlem2x.p: |- .+ = ( +g ` D )
  assume lclkrlem2x.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrlem2x.x: |- ( ph -> X e. V )
  assume lclkrlem2x.y: |- ( ph -> Y e. V )
  assume lclkrlem2x.e: |- ( ph -> E e. F )
  assume lclkrlem2x.g: |- ( ph -> G e. F )
  assume lclkrlem2x.le: |- ( ph -> ( L ` E ) = ( ._|_ ` { X } ) )
  assume lclkrlem2x.lg: |- ( ph -> ( L ` G ) = ( ._|_ ` { Y } ) )


  assert |- ( ph -> ( ._|_ ` ( ._|_ ` ( L ` ( E .+ G ) ) ) ) = ( L ` ( E .+ G ) ) )

  proof
    wph
    cX
    cE
    cG
    c.pl
    co
    #
    cfv
    #
    cU
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    cY
    @0
    cfv
    #
    @3
    wceq
    #
    @0
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @7
    wceq
    #
    @4
    wn
    wph
    @1
    @3
    wne
    #
    @8
    @1
    @3
    df-ne
    wph
    @9
    wa
    cD
    c.pl
    cU
    clsm
    cfv
    #
    @2
    cU
    cvsca
    cfv
    #
    @2
    cmulr
    cfv
    #
    cU
    cE
    cF
    cG
    cH
    @2
    cinvr
    cfv
    #
    cK
    cL
    cU
    csg
    cfv
    #
    cU
    clspn
    cfv
    #
    c.pe
    cV
    cW
    cX
    cY
    @3
    lclkrlem2x.v
    @11
    eqid
    #
    @2
    eqid
    #
    @12
    eqid
    #
    @3
    eqid
    #
    @13
    eqid
    #
    @14
    eqid
    #
    lclkrlem2x.f
    lclkrlem2x.d
    lclkrlem2x.p
    wph
    cX
    cV
    wcel
    #
    @9
    lclkrlem2x.x
    adantr
    wph
    cY
    cV
    wcel
    #
    @9
    lclkrlem2x.y
    adantr
    wph
    cE
    cF
    wcel
    #
    @9
    lclkrlem2x.e
    adantr
    wph
    cG
    cF
    wcel
    #
    @9
    lclkrlem2x.g
    adantr
    @15
    eqid
    #
    lclkrlem2x.l
    lclkrlem2x.h
    lclkrlem2x.o
    lclkrlem2x.u
    @10
    eqid
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @9
    lclkrlem2x.k
    adantr
    wph
    cE
    cL
    cfv
    cX
    csn
    c.pe
    cfv
    wceq
    #
    @9
    lclkrlem2x.le
    adantr
    wph
    cG
    cL
    cfv
    cY
    csn
    c.pe
    cfv
    wceq
    #
    @9
    lclkrlem2x.lg
    adantr
    wph
    @9
    simpr
    lclkrlem2u
    sylan2br
    @6
    wn
    wph
    @5
    @3
    wne
    #
    @8
    @5
    @3
    df-ne
    wph
    @31
    wa
    cD
    c.pl
    @10
    @2
    @11
    @12
    cU
    cE
    cF
    cG
    cH
    @13
    cK
    cL
    @14
    @15
    c.pe
    cV
    cW
    cX
    cY
    @3
    lclkrlem2x.v
    @16
    @17
    @18
    @19
    @20
    @21
    lclkrlem2x.f
    lclkrlem2x.d
    lclkrlem2x.p
    wph
    @22
    @31
    lclkrlem2x.x
    adantr
    wph
    @23
    @31
    lclkrlem2x.y
    adantr
    wph
    @24
    @31
    lclkrlem2x.e
    adantr
    wph
    @25
    @31
    lclkrlem2x.g
    adantr
    @26
    lclkrlem2x.l
    lclkrlem2x.h
    lclkrlem2x.o
    lclkrlem2x.u
    @27
    wph
    @28
    @31
    lclkrlem2x.k
    adantr
    wph
    @29
    @31
    lclkrlem2x.le
    adantr
    wph
    @30
    @31
    lclkrlem2x.lg
    adantr
    wph
    @31
    simpr
    lclkrlem2t
    sylan2br
    wph
    @4
    @6
    wa
    #
    wa
    cD
    c.pl
    @10
    @2
    @11
    @12
    cU
    cE
    cF
    cG
    cH
    @13
    cK
    cL
    @14
    @15
    c.pe
    cV
    cW
    cX
    cY
    @3
    lclkrlem2x.v
    @16
    @17
    @18
    @19
    @20
    @21
    lclkrlem2x.f
    lclkrlem2x.d
    lclkrlem2x.p
    wph
    @22
    @32
    lclkrlem2x.x
    adantr
    wph
    @23
    @32
    lclkrlem2x.y
    adantr
    wph
    @24
    @32
    lclkrlem2x.e
    adantr
    wph
    @25
    @32
    lclkrlem2x.g
    adantr
    @26
    lclkrlem2x.l
    lclkrlem2x.h
    lclkrlem2x.o
    lclkrlem2x.u
    @27
    wph
    @28
    @32
    lclkrlem2x.k
    adantr
    wph
    @29
    @32
    lclkrlem2x.le
    adantr
    wph
    @30
    @32
    lclkrlem2x.lg
    adantr
    wph
    @4
    @6
    simprl
    wph
    @4
    @6
    simprr
    lclkrlem2w
    pm2.61dda
end
