include "wer.mm"
include "cv.mm"
include "cop.mm"
include "c1o.mm"
include "cdif.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "co.mm"
include "wbr.mm"
include "c2o.mm"
include "wral.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "wa.mm"
include "cab.mm"
include "ciin.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "efglem.mm"
include "abn0.mm"
include "mpbir.mm"
include "wi.mm"
include "ereq1.mm"
include "ralab2.mm"
include "simpl.mm"
include "mpgbir.mm"
include "iiner.mm"
include "mp2an.mm"
include "wceq.mm"
include "wb.mm"
include "cint.mm"
include "efgval.mm"
include "intiin.mm"
include "eqtri.mm"
include "ax-mp.mm"

theorem efger
  let c.sm: class .~
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
  let cA: class A
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
  let cB: class B
  let cC: class C
  let cS: class S
  let cY: class Y
  let cD: class D
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume efgval.r: |- .~ = ( ~FG ` I )


  assert |- .~ Er W

  proof
    cW
    c.sm
    wer
    #
    cW
    vw
    cW
    vr
    cv
    #
    wer
    #
    vx
    cv
    #
    @3
    vn
    cv
    #
    @4
    vy
    cv
    #
    vz
    cv
    #
    cop
    @5
    c1o
    @6
    cdif
    cop
    cs2
    cotp
    csplice
    co
    @1
    wbr
    vz
    c2o
    wral
    vy
    cI
    wral
    vn
    cc0
    @3
    chash
    cfv
    cfz
    co
    wral
    vx
    cW
    wral
    #
    wa
    #
    vr
    cab
    #
    vw
    cv
    #
    ciin
    #
    wer
    #
    @9
    c0
    wne
    #
    cW
    @10
    wer
    #
    vw
    @9
    wral
    #
    @12
    @13
    @8
    vr
    wex
    vx
    vy
    vz
    vn
    cI
    cW
    vr
    efgval.w
    efglem
    @8
    vr
    abn0
    mpbir
    @15
    @8
    @2
    wi
    vr
    @8
    @14
    @2
    vw
    vr
    cW
    @10
    @1
    ereq1
    ralab2
    @2
    @7
    simpl
    mpgbir
    vw
    @9
    cW
    @10
    iiner
    mp2an
    c.sm
    @11
    wceq
    @0
    @12
    wb
    c.sm
    @9
    cint
    @11
    vx
    vy
    vz
    c.sm
    vn
    cI
    cW
    vr
    efgval.w
    efgval.r
    efgval
    vw
    @9
    intiin
    eqtri
    cW
    c.sm
    @11
    ereq1
    ax-mp
    mpbir
end
