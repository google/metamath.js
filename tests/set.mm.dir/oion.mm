include "wcel.mm"
include "cdm.mm"
include "con0.mm"
include "word.mm"
include "oicl.mm"
include "cvv.mm"
include "wb.mm"
include "oiexg.mm"
include "dmexg.mm"
include "elong.mm"
include "3syl.mm"
include "mpbiri.mm"

theorem oion
  let cA: class A
  let cR: class R
  let cF: class F
  let cV: class V
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vh: setvar h
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z
  let cM: class M
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  let vy: setvar y
  let cN: class N
  assume oicl.1: |- F = OrdIso ( R , A )


  assert |- ( A e. V -> dom F e. On )

  proof
    cA
    cV
    wcel
    #
    cF
    cdm
    #
    con0
    wcel
    #
    @1
    word
    #
    cA
    cR
    cF
    oicl.1
    oicl
    @0
    cF
    cvv
    wcel
    @1
    cvv
    wcel
    @2
    @3
    wb
    cA
    cR
    cF
    cV
    oicl.1
    oiexg
    cF
    cvv
    dmexg
    @1
    cvv
    elong
    3syl
    mpbiri
end
