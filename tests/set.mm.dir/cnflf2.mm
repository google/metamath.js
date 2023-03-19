include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cflf.mm"
include "cflim.mm"
include "wral.mm"
include "cfil.mm"
include "cima.mm"
include "wss.mm"
include "cnflf.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "ffun.mm"
include "adantl.mm"
include "cuni.mm"
include "eqid.mm"
include "flimelbas.mm"
include "ssriv.mm"
include "wceq.mm"
include "fdm.mm"
include "toponuni.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "syl5sseqr.mm"
include "funimass4.mm"
include "syl2anc.mm"
include "ralbidv.mm"
include "pm5.32da.mm"
include "bitr4d.mm"

theorem cnflf2
  let vf: setvar f
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cL: class L

  disjoint X f
  disjoint Y f
  disjoint F f
  disjoint J f
  disjoint K f
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint L u
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X z
  disjoint Y u
  disjoint Y v
  disjoint Y x
  disjoint Y z
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K y
  disjoint K z
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. f e. ( Fil ` X ) ( F " ( J fLim f ) ) C_ ( ( K fLimf f ) ` F ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    cX
    cY
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    cF
    cK
    vf
    cv
    #
    cflf
    co
    cfv
    #
    wcel
    vx
    cJ
    @5
    cflim
    co
    #
    wral
    #
    vf
    cX
    cfil
    cfv
    #
    wral
    #
    wa
    @3
    cF
    @7
    cima
    @6
    wss
    #
    vf
    @9
    wral
    #
    wa
    vx
    vf
    cF
    cJ
    cK
    cX
    cY
    cnflf
    @2
    @3
    @12
    @10
    @2
    @3
    wa
    #
    @11
    @8
    vf
    @9
    @13
    cF
    wfun
    #
    @7
    cF
    cdm
    #
    wss
    @11
    @8
    wb
    @3
    @14
    @2
    cX
    cY
    cF
    ffun
    adantl
    @13
    cJ
    cuni
    #
    @7
    @15
    vx
    @7
    @16
    @4
    @5
    cJ
    @16
    @16
    eqid
    flimelbas
    ssriv
    @13
    @15
    cX
    @16
    @3
    @15
    cX
    wceq
    @2
    cX
    cY
    cF
    fdm
    adantl
    @0
    cX
    @16
    wceq
    @1
    @3
    cX
    cJ
    toponuni
    ad2antrr
    eqtrd
    syl5sseqr
    vx
    @7
    @6
    cF
    funimass4
    syl2anc
    ralbidv
    pm5.32da
    bitr4d
end
