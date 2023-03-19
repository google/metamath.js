include "wcel.mm"
include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "cvv.mm"
include "cdm.mm"
include "wf1.mm"
include "cep.mm"
include "wiso.mm"
include "wf1o.mm"
include "ordtype.mm"
include "isof1o.mm"
include "f1of1.mm"
include "3syl.mm"
include "f1dmex.mm"
include "wf.mm"
include "f1f.mm"
include "fex.mm"
include "sylan.mm"
include "syldan.mm"
include "expcom.mm"
include "syl5.mm"
include "wn.mm"
include "c0.mm"
include "oi0.mm"
include "0ex.mm"
include "syl6eqel.mm"
include "pm2.61d1.mm"

theorem oiexg
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


  assert |- ( A e. V -> F e. _V )

  proof
    cA
    cV
    wcel
    #
    cA
    cR
    wwe
    cA
    cR
    wse
    wa
    #
    cF
    cvv
    wcel
    #
    @1
    cF
    cdm
    #
    cA
    cF
    wf1
    #
    @0
    @2
    @1
    @3
    cA
    cep
    cR
    cF
    wiso
    @3
    cA
    cF
    wf1o
    @4
    cA
    cR
    cF
    oicl.1
    ordtype
    @3
    cA
    cep
    cR
    cF
    isof1o
    @3
    cA
    cF
    f1of1
    3syl
    @4
    @0
    @2
    @4
    @0
    @3
    cvv
    wcel
    #
    @2
    @3
    cA
    cV
    cF
    f1dmex
    @4
    @3
    cA
    cF
    wf
    @5
    @2
    @3
    cA
    cF
    f1f
    @3
    cA
    cvv
    cF
    fex
    sylan
    syldan
    expcom
    syl5
    @1
    wn
    cF
    c0
    cvv
    cA
    cR
    cF
    oicl.1
    oi0
    0ex
    syl6eqel
    pm2.61d1
end
