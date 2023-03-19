include "cphl.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cstf.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "wf1.mm"
include "wb.mm"
include "csr.mm"
include "wf1o.mm"
include "phlsrng.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "srngf1o.mm"
include "f1of1.mm"
include "3syl.mm"
include "ipcl.mm"
include "clmod.mm"
include "phllmod.mm"
include "lmod0cl.mm"
include "syl.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "cstv.mm"
include "stafval.mm"
include "ipcj.mm"
include "eqtrd.mm"
include "srng0.mm"
include "eqeq12d.mm"
include "bitr3d.mm"

theorem iporthcom
  let cA: class A
  let cB: class B
  let cF: class F
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cG: class G
  let c.as: class .*
  let cK: class K
  let c.0: class .0.
  let c.x: class .x.
  assume phlsrng.f: |- F = ( Scalar ` W )
  assume phllmhm.h: |- ., = ( .i ` W )
  assume phllmhm.v: |- V = ( Base ` W )
  assume ip0l.z: |- Z = ( 0g ` F )


  assert |- ( ( W e. PreHil /\ A e. V /\ B e. V ) -> ( ( A ., B ) = Z <-> ( B ., A ) = Z ) )

  proof
    cW
    cphl
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cA
    cB
    c.xi
    co
    #
    cF
    cstf
    cfv
    #
    cfv
    #
    cZ
    @5
    cfv
    #
    wceq
    #
    @4
    cZ
    wceq
    #
    cB
    cA
    c.xi
    co
    #
    cZ
    wceq
    @3
    cF
    cbs
    cfv
    #
    @11
    @5
    wf1
    #
    @4
    @11
    wcel
    #
    cZ
    @11
    wcel
    #
    @8
    @9
    wb
    @3
    cF
    csr
    wcel
    #
    @11
    @11
    @5
    wf1o
    @12
    @0
    @1
    @15
    @2
    cF
    cW
    phlsrng.f
    phlsrng
    3ad2ant1
    #
    @11
    cF
    @5
    @5
    eqid
    #
    @11
    eqid
    #
    srngf1o
    @11
    @11
    @5
    f1of1
    3syl
    cA
    cB
    cF
    c.xi
    @11
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @18
    ipcl
    #
    @3
    cW
    clmod
    wcel
    #
    @14
    @0
    @1
    @20
    @2
    cW
    phllmod
    3ad2ant1
    cF
    @11
    cW
    cZ
    phlsrng.f
    @18
    ip0l.z
    lmod0cl
    syl
    #
    @11
    @11
    @4
    cZ
    @5
    f1fveq
    syl12anc
    @3
    @6
    @10
    @7
    cZ
    @3
    @6
    @4
    cF
    cstv
    cfv
    #
    cfv
    #
    @10
    @3
    @13
    @6
    @23
    wceq
    @19
    @4
    @11
    cF
    @5
    @22
    @18
    @22
    eqid
    #
    @17
    stafval
    syl
    cA
    cB
    cF
    c.xi
    @22
    cV
    cW
    phlsrng.f
    phllmhm.h
    phllmhm.v
    @24
    ipcj
    eqtrd
    @3
    @7
    cZ
    @22
    cfv
    #
    cZ
    @3
    @14
    @7
    @25
    wceq
    @21
    cZ
    @11
    cF
    @5
    @22
    @18
    @24
    @17
    stafval
    syl
    @3
    @15
    @25
    cZ
    wceq
    @16
    cF
    @22
    cZ
    @24
    ip0l.z
    srng0
    syl
    eqtrd
    eqeq12d
    bitr3d
end
