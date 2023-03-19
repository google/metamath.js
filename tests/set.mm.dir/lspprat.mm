include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "c0g.mm"
include "cdif.mm"
include "c0.mm"
include "wss.mm"
include "ssdif0.mm"
include "wa.mm"
include "wcel.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eqid.mm"
include "lmod0vcl.mm"
include "adantr.mm"
include "simpr.mm"
include "lss0ss.mm"
include "syl2anc.mm"
include "eqssd.mm"
include "lspsn0.mm"
include "eqtr4d.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "syl5bir.mm"
include "wex.mm"
include "wne.mm"
include "lssss.mm"
include "ssdifssd.mm"
include "sseld.mm"
include "lsppratlem6.mm"
include "jcad.mm"
include "eximdv.mm"
include "n0.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "pm2.61dne.mm"

theorem lspprat
  let wph: wff ph
  let vz: setvar z
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspprat.v: |- V = ( Base ` W )
  assume lspprat.s: |- S = ( LSubSp ` W )
  assume lspprat.n: |- N = ( LSpan ` W )
  assume lspprat.w: |- ( ph -> W e. LVec )
  assume lspprat.u: |- ( ph -> U e. S )
  assume lspprat.x: |- ( ph -> X e. V )
  assume lspprat.y: |- ( ph -> Y e. V )
  assume lspprat.p: |- ( ph -> U C. ( N ` { X , Y } ) )

  disjoint N z
  disjoint U z
  disjoint V z
  disjoint W z
  disjoint ph z
  assert |- ( ph -> E. z e. V U = ( N ` { z } ) )

  proof
    wph
    cU
    vz
    cv
    #
    csn
    #
    cN
    cfv
    #
    wceq
    #
    vz
    cV
    wrex
    #
    cU
    cW
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    c0
    @7
    c0
    wceq
    cU
    @6
    wss
    #
    wph
    @4
    cU
    @6
    ssdif0
    wph
    @8
    @4
    wph
    @8
    wa
    #
    @5
    cV
    wcel
    #
    cU
    @6
    cN
    cfv
    #
    wceq
    #
    @4
    wph
    @10
    @8
    wph
    cW
    clmod
    wcel
    #
    @10
    wph
    cW
    clvec
    wcel
    @13
    lspprat.w
    cW
    lveclmod
    syl
    #
    cV
    cW
    @5
    lspprat.v
    @5
    eqid
    #
    lmod0vcl
    syl
    adantr
    @9
    cU
    @6
    @11
    @9
    cU
    @6
    wph
    @8
    simpr
    wph
    @6
    cU
    wss
    #
    @8
    wph
    @13
    cU
    cS
    wcel
    #
    @16
    @14
    lspprat.u
    cS
    cW
    cU
    @5
    @15
    lspprat.s
    lss0ss
    syl2anc
    adantr
    eqssd
    wph
    @11
    @6
    wceq
    #
    @8
    wph
    @13
    @18
    @14
    cN
    cW
    @5
    @15
    lspprat.n
    lspsn0
    syl
    adantr
    eqtr4d
    @3
    @12
    vz
    @5
    cV
    @0
    @5
    wceq
    #
    @2
    @11
    cU
    @19
    @1
    @6
    cN
    @0
    @5
    sneq
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    ex
    syl5bir
    wph
    @0
    @7
    wcel
    #
    vz
    wex
    @0
    cV
    wcel
    #
    @3
    wa
    #
    vz
    wex
    @7
    c0
    wne
    @4
    wph
    @20
    @22
    vz
    wph
    @20
    @21
    @3
    wph
    @7
    cV
    @0
    wph
    cU
    cV
    @6
    wph
    @17
    cU
    cV
    wss
    lspprat.u
    cS
    cU
    cV
    cW
    lspprat.v
    lspprat.s
    lssss
    syl
    ssdifssd
    sseld
    wph
    vz
    cS
    cU
    cN
    cV
    cW
    cX
    cY
    @5
    lspprat.v
    lspprat.s
    lspprat.n
    lspprat.w
    lspprat.u
    lspprat.x
    lspprat.y
    lspprat.p
    @15
    lsppratlem6
    jcad
    eximdv
    vz
    @7
    n0
    @3
    vz
    cV
    df-rex
    3imtr4g
    pm2.61dne
end
