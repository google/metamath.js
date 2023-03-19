include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cc.mm"
include "cclm.mm"
include "wss.mm"
include "tchclm.mm"
include "adantr.mm"
include "eqid.mm"
include "clmsscn.mm"
include "syl.mm"
include "cphl.mm"
include "ipcl.mm"
include "3anidm23.mm"
include "sylan.mm"
include "sseldd.mm"
include "ccj.mm"
include "cstv.mm"
include "wceq.mm"
include "clmcj.mm"
include "fveq1d.mm"
include "simpr.mm"
include "ipcj.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "cjrebd.mm"

theorem tchcphlem3
  let wph: wff ph
  let cF: class F
  let cG: class G
  let c.xi: class .,
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let c.mi: class .-
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let c.x: class .x.
  let cY: class Y
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchcph.v: |- V = ( Base ` W )
  assume tchcph.f: |- F = ( Scalar ` W )
  assume tchcph.1: |- ( ph -> W e. PreHil )
  assume tchcph.2: |- ( ph -> F = ( CCfld |`s K ) )
  assume tchcph.h: |- ., = ( .i ` W )


  assert |- ( ( ph /\ X e. V ) -> ( X ., X ) e. RR )

  proof
    wph
    cX
    cV
    wcel
    #
    wa
    #
    cX
    cX
    c.xi
    co
    #
    @1
    cF
    cbs
    cfv
    #
    cc
    @2
    @1
    cW
    cclm
    wcel
    #
    @3
    cc
    wss
    wph
    @4
    @0
    wph
    cF
    cG
    cK
    cV
    cW
    tchval.n
    tchcph.v
    tchcph.f
    tchcph.1
    tchcph.2
    tchclm
    adantr
    #
    cF
    @3
    cW
    tchcph.f
    @3
    eqid
    #
    clmsscn
    syl
    wph
    cW
    cphl
    wcel
    #
    @0
    @2
    @3
    wcel
    #
    tchcph.1
    @7
    @0
    @8
    cX
    cX
    cF
    c.xi
    @3
    cV
    cW
    tchcph.f
    tchcph.h
    tchcph.v
    @6
    ipcl
    3anidm23
    sylan
    sseldd
    @1
    @2
    ccj
    cfv
    @2
    cF
    cstv
    cfv
    #
    cfv
    #
    @2
    @1
    @2
    ccj
    @9
    @1
    @4
    ccj
    @9
    wceq
    @5
    cF
    cW
    tchcph.f
    clmcj
    syl
    fveq1d
    @1
    @7
    @0
    @0
    @10
    @2
    wceq
    wph
    @7
    @0
    tchcph.1
    adantr
    wph
    @0
    simpr
    #
    @11
    cX
    cX
    cF
    c.xi
    @9
    cV
    cW
    tchcph.f
    tchcph.h
    tchcph.v
    @9
    eqid
    ipcj
    syl3anc
    eqtrd
    cjrebd
end
