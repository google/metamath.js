include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cfunc.mm"
include "wrel.mm"
include "wcel.mm"
include "wceq.mm"
include "relfunc.mm"
include "wa.mm"
include "natrcl.mm"
include "syl.mm"
include "simpld.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "simprd.mm"
include "oveq12d.mm"
include "eleqtrd.mm"

theorem nat1st2nd
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cR: class R
  let va: setvar a
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let cK: class K
  let cX: class X
  let cL: class L
  let c.x: class .x.
  let cY: class Y
  let cB: class B
  let cJ: class J
  assume natrcl.1: |- N = ( C Nat D )
  assume nat1st2nd.2: |- ( ph -> A e. ( F N G ) )


  assert |- ( ph -> A e. ( <. ( 1st ` F ) , ( 2nd ` F ) >. N <. ( 1st ` G ) , ( 2nd ` G ) >. ) )

  proof
    wph
    cA
    cF
    cG
    cN
    co
    #
    cF
    c1st
    cfv
    cF
    c2nd
    cfv
    cop
    #
    cG
    c1st
    cfv
    cG
    c2nd
    cfv
    cop
    #
    cN
    co
    nat1st2nd.2
    wph
    cF
    @1
    cG
    @2
    cN
    wph
    cC
    cD
    cfunc
    co
    #
    wrel
    #
    cF
    @3
    wcel
    #
    cF
    @1
    wceq
    cC
    cD
    relfunc
    #
    wph
    @5
    cG
    @3
    wcel
    #
    wph
    cA
    @0
    wcel
    @5
    @7
    wa
    nat1st2nd.2
    cA
    cC
    cD
    cF
    cG
    cN
    natrcl.1
    natrcl
    syl
    #
    simpld
    cF
    @3
    1st2nd
    sylancr
    wph
    @4
    @7
    cG
    @2
    wceq
    @6
    wph
    @5
    @7
    @8
    simprd
    cG
    @3
    1st2nd
    sylancr
    oveq12d
    eleqtrd
end
