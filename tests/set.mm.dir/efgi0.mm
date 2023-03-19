include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "w3a.mm"
include "c0.mm"
include "cop.mm"
include "c1o.mm"
include "cdif.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "wbr.mm"
include "wa.mm"
include "c2o.mm"
include "cpr.mm"
include "0ex.mm"
include "prid1.mm"
include "df2o3.mm"
include "eleqtrri.mm"
include "efgi.mm"
include "mpanr2.mm"
include "3impa.mm"
include "wtru.mm"
include "wceq.mm"
include "tru.mm"
include "eqidd.mm"
include "dif0.mm"
include "opeq2i.mm"
include "a1i.mm"
include "s2eqd.mm"
include "oteq3.mm"
include "mp2b.mm"
include "oveq2i.mm"
include "syl6breq.mm"

theorem efgi0
  let cA: class A
  let c.sm: class .~
  let cI: class I
  let cJ: class J
  let cN: class N
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
  let cU: class U
  let vk: setvar k
  let vo: setvar o
  let cT: class T
  let cV: class V
  let cX: class X
  let cQ: class Q
  let cB: class B
  let cC: class C
  let cS: class S
  let cY: class Y
  let cD: class D
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume efgval.r: |- .~ = ( ~FG ` I )


  assert |- ( ( A e. W /\ N e. ( 0 ... ( # ` A ) ) /\ J e. I ) -> A .~ ( A splice <. N , N , <" <. J , (/) >. <. J , 1o >. "> >. ) )

  proof
    cA
    cW
    wcel
    #
    cN
    cc0
    cA
    chash
    cfv
    cfz
    co
    wcel
    #
    cJ
    cI
    wcel
    #
    w3a
    cA
    cA
    cN
    cN
    cJ
    c0
    cop
    #
    cJ
    c1o
    c0
    cdif
    #
    cop
    #
    cs2
    #
    cotp
    #
    csplice
    co
    #
    cA
    cN
    cN
    @3
    cJ
    c1o
    cop
    #
    cs2
    #
    cotp
    #
    csplice
    co
    c.sm
    @0
    @1
    @2
    cA
    @8
    c.sm
    wbr
    #
    @0
    @1
    wa
    @2
    c0
    c2o
    wcel
    @12
    c0
    c0
    c1o
    cpr
    c2o
    c0
    c1o
    0ex
    prid1
    df2o3
    eleqtrri
    cA
    c.sm
    cI
    cJ
    c0
    cN
    cW
    efgval.w
    efgval.r
    efgi
    mpanr2
    3impa
    @7
    @11
    cA
    csplice
    wtru
    @6
    @10
    wceq
    @7
    @11
    wceq
    tru
    wtru
    @3
    @5
    @3
    @9
    wtru
    @3
    eqidd
    @5
    @9
    wceq
    wtru
    @4
    c1o
    cJ
    c1o
    dif0
    opeq2i
    a1i
    s2eqd
    @6
    @10
    cN
    cN
    oteq3
    mp2b
    oveq2i
    syl6breq
end
