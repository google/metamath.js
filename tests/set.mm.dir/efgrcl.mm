include "wcel.mm"
include "cvv.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "wceq.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "2on0.mm"
include "dmxp.mm"
include "ax-mp.mm"
include "cid.mm"
include "cfv.mm"
include "elfvex.mm"
include "eleq2s.mm"
include "wrdexb.mm"
include "sylibr.mm"
include "dmexg.mm"
include "syl.mm"
include "syl5eqelr.mm"
include "fvi.mm"
include "syl5eq.mm"
include "jca.mm"

theorem efgrcl
  let cA: class A
  let cI: class I
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cL: class L
  let cF: class F
  let cK: class K
  let vn: setvar n
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let cP: class P
  let wph: wff ph
  let vm: setvar m
  let vx: setvar x
  let cM: class M
  let cN: class N
  let cU: class U
  let vk: setvar k
  let vo: setvar o
  let cT: class T
  let cV: class V
  let cX: class X
  let cQ: class Q
  let c.sm: class .~
  let cB: class B
  let cC: class C
  let cS: class S
  let cY: class Y
  let cD: class D
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )


  assert |- ( A e. W -> ( I e. _V /\ W = Word ( I X. 2o ) ) )

  proof
    cA
    cW
    wcel
    #
    cI
    cvv
    wcel
    cW
    cI
    c2o
    cxp
    #
    cword
    #
    wceq
    @0
    cI
    @1
    cdm
    #
    cvv
    c2o
    c0
    wne
    @3
    cI
    wceq
    2on0
    cI
    c2o
    dmxp
    ax-mp
    @0
    @1
    cvv
    wcel
    #
    @3
    cvv
    wcel
    @0
    @2
    cvv
    wcel
    #
    @4
    @5
    cA
    @2
    cid
    cfv
    #
    cW
    cA
    @2
    cid
    elfvex
    efgval.w
    eleq2s
    #
    @1
    wrdexb
    sylibr
    @1
    cvv
    dmexg
    syl
    syl5eqelr
    @0
    cW
    @6
    @2
    efgval.w
    @0
    @5
    @6
    @2
    wceq
    @7
    @2
    cvv
    fvi
    syl
    syl5eq
    jca
end
