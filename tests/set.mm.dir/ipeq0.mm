include "cphl.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cmpt.mm"
include "crglmod.mm"
include "cfv.mm"
include "clmhm.mm"
include "cstv.mm"
include "w3a.mm"
include "clvec.mm"
include "csr.mm"
include "eqid.mm"
include "isphl.mm"
include "simp3bi.mm"
include "simp2.mm"
include "ralimi.mm"
include "syl.mm"
include "oveq12.mm"
include "anidms.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "ip0l.mm"
include "oveq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem ipeq0
  let cA: class A
  let cF: class F
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cG: class G
  let c.as: class .*
  let cK: class K
  let c.x: class .x.
  assume phlsrng.f: |- F = ( Scalar ` W )
  assume phllmhm.h: |- ., = ( .i ` W )
  assume phllmhm.v: |- V = ( Base ` W )
  assume ip0l.z: |- Z = ( 0g ` F )
  assume ip0l.o: |- .0. = ( 0g ` W )


  assert |- ( ( W e. PreHil /\ A e. V ) -> ( ( A ., A ) = Z <-> A = .0. ) )

  proof
    cW
    cphl
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cA
    cA
    c.xi
    co
    #
    cZ
    wceq
    #
    cA
    c.0
    wceq
    #
    @0
    vx
    cv
    #
    @6
    c.xi
    co
    #
    cZ
    wceq
    #
    @6
    c.0
    wceq
    #
    wi
    #
    vx
    cV
    wral
    #
    @1
    @4
    @5
    wi
    #
    @0
    vy
    cV
    vy
    cv
    #
    @6
    c.xi
    co
    #
    cmpt
    cW
    cF
    crglmod
    cfv
    clmhm
    co
    wcel
    #
    @10
    @6
    @13
    c.xi
    co
    cF
    cstv
    cfv
    #
    cfv
    @14
    wceq
    vy
    cV
    wral
    #
    w3a
    #
    vx
    cV
    wral
    #
    @11
    @0
    cW
    clvec
    wcel
    cF
    csr
    wcel
    @19
    vx
    vy
    cF
    c.xi
    @16
    cV
    cW
    c.0
    cZ
    phllmhm.v
    phlsrng.f
    phllmhm.h
    ip0l.o
    @16
    eqid
    ip0l.z
    isphl
    simp3bi
    @18
    @10
    vx
    cV
    @15
    @10
    @17
    simp2
    ralimi
    syl
    @10
    @12
    vx
    cA
    cV
    @6
    cA
    wceq
    #
    @8
    @4
    @9
    @5
    @20
    @7
    @3
    cZ
    @20
    @7
    @3
    wceq
    @6
    cA
    @6
    cA
    c.xi
    oveq12
    anidms
    eqeq1d
    @6
    cA
    c.0
    eqeq1
    imbi12d
    rspccva
    sylan
    @2
    @4
    @5
    c.0
    cA
    c.xi
    co
    #
    cZ
    wceq
    cA
    cF
    c.xi
    cV
    cW
    c.0
    cZ
    phlsrng.f
    phllmhm.h
    phllmhm.v
    ip0l.z
    ip0l.o
    ip0l
    @5
    @3
    @21
    cZ
    cA
    c.0
    cA
    c.xi
    oveq1
    eqeq1d
    syl5ibrcom
    impbid
end
