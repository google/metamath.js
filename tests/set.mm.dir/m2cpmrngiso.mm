include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "crs.mm"
include "co.mm"
include "crh.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "m2cpmrhm.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "m2cpmf1o.mm"
include "wceq.mm"
include "wb.mm"
include "wss.mm"
include "cv.mm"
include "eqid.mm"
include "cpmatpmat.mm"
include "3expia.mm"
include "ssrdv.mm"
include "ressbas2.mm"
include "syl.mm"
include "eqcomd.mm"
include "f1oeq3.mm"
include "mpbird.mm"
include "cgrp.mm"
include "matring.mm"
include "csubg.mm"
include "cpmatsubgpmat.mm"
include "subggrp.mm"
include "3syl.mm"
include "isrim.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem m2cpmrngiso
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cK: class K
  let cN: class N
  let vc: setvar c
  let vm: setvar m
  let vx: setvar x
  let vi: setvar i
  let vj: setvar j
  assume m2cpmfo.s: |- S = ( N ConstPolyMat R )
  assume m2cpmfo.t: |- T = ( N matToPolyMat R )
  assume m2cpmfo.a: |- A = ( N Mat R )
  assume m2cpmfo.k: |- K = ( Base ` A )
  assume m2cpmrngiso.p: |- P = ( Poly1 ` R )
  assume m2cpmrngiso.c: |- C = ( N Mat P )
  assume m2cpmrngiso.u: |- U = ( C |`s S )


  assert |- ( ( N e. Fin /\ R e. CRing ) -> T e. ( A RingIso U ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cT
    cA
    cU
    crs
    co
    wcel
    #
    cT
    cA
    cU
    crh
    co
    wcel
    #
    cK
    cU
    cbs
    cfv
    #
    cT
    wf1o
    #
    cA
    cK
    cC
    cP
    cR
    cS
    cT
    cU
    cN
    m2cpmfo.s
    m2cpmfo.t
    m2cpmfo.a
    m2cpmfo.k
    m2cpmrngiso.p
    m2cpmrngiso.c
    m2cpmrngiso.u
    m2cpmrhm
    @2
    @0
    cR
    crg
    wcel
    #
    wa
    #
    @6
    @1
    @7
    @0
    cR
    crngring
    anim2i
    #
    @8
    @6
    cK
    cS
    cT
    wf1o
    #
    cA
    cR
    cS
    cT
    cK
    cN
    m2cpmfo.s
    m2cpmfo.t
    m2cpmfo.a
    m2cpmfo.k
    m2cpmf1o
    @8
    @5
    cS
    wceq
    @6
    @10
    wb
    @8
    cS
    @5
    @8
    cS
    cC
    cbs
    cfv
    #
    wss
    cS
    @5
    wceq
    @8
    vm
    cS
    @11
    @0
    @7
    vm
    cv
    #
    cS
    wcel
    @12
    @11
    wcel
    @11
    cC
    cP
    cR
    cS
    @12
    cN
    crg
    m2cpmfo.s
    m2cpmrngiso.p
    m2cpmrngiso.c
    @11
    eqid
    #
    cpmatpmat
    3expia
    ssrdv
    cS
    @11
    cU
    cC
    m2cpmrngiso.u
    @13
    ressbas2
    syl
    eqcomd
    @5
    cS
    cK
    cT
    f1oeq3
    syl
    mpbird
    syl
    @2
    cA
    crg
    wcel
    #
    cU
    cgrp
    wcel
    #
    @3
    @4
    @6
    wa
    wb
    @2
    @8
    @14
    @9
    cA
    cR
    cN
    m2cpmfo.a
    matring
    syl
    @2
    @8
    cS
    cC
    csubg
    cfv
    wcel
    @15
    @9
    cC
    cP
    cR
    cS
    cN
    m2cpmfo.s
    m2cpmrngiso.p
    m2cpmrngiso.c
    cpmatsubgpmat
    cS
    cC
    cU
    m2cpmrngiso.u
    subggrp
    3syl
    cK
    @5
    cA
    cU
    cT
    crg
    cgrp
    m2cpmfo.k
    @5
    eqid
    isrim
    syl2anc
    mpbir2and
end
