include "crg.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "coe1tm.mm"
include "fveq1d.mm"
include "simp3.mm"
include "simp2.mm"
include "iftrue.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem coe1tmfv1
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.ex: class .^
  let cK: class K
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cA: class A
  let cY: class Y
  let wph: wff ph
  let c.xp: class .X.
  let c.xb: class .xb
  assume coe1tm.z: |- .0. = ( 0g ` R )
  assume coe1tm.k: |- K = ( Base ` R )
  assume coe1tm.p: |- P = ( Poly1 ` R )
  assume coe1tm.x: |- X = ( var1 ` R )
  assume coe1tm.m: |- .x. = ( .s ` P )
  assume coe1tm.n: |- N = ( mulGrp ` P )
  assume coe1tm.e: |- .^ = ( .g ` N )


  assert |- ( ( R e. Ring /\ C e. K /\ D e. NN0 ) -> ( ( coe1 ` ( C .x. ( D .^ X ) ) ) ` D ) = C )

  proof
    cR
    crg
    wcel
    #
    cC
    cK
    wcel
    #
    cD
    cn0
    wcel
    #
    w3a
    #
    cD
    cC
    cD
    cX
    c.ex
    co
    c.x
    co
    cco1
    cfv
    #
    cfv
    cD
    vx
    cn0
    vx
    cv
    cD
    wceq
    #
    cC
    c.0
    cif
    #
    cmpt
    #
    cfv
    #
    cC
    @3
    cD
    @4
    @7
    vx
    cC
    cD
    cP
    cR
    c.x
    c.ex
    cK
    cN
    cX
    c.0
    coe1tm.z
    coe1tm.k
    coe1tm.p
    coe1tm.x
    coe1tm.m
    coe1tm.n
    coe1tm.e
    coe1tm
    fveq1d
    @3
    @2
    @1
    @8
    cC
    wceq
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    vx
    cD
    @6
    cC
    cn0
    cK
    @7
    @5
    cC
    c.0
    iftrue
    @7
    eqid
    fvmptg
    syl2anc
    eqtrd
end
