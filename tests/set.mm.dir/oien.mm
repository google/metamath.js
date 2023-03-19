include "wcel.mm"
include "wwe.mm"
include "wa.mm"
include "cvv.mm"
include "cdm.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "oiexg.mm"
include "adantr.mm"
include "cep.mm"
include "wiso.mm"
include "oiiso.mm"
include "isof1o.mm"
include "syl.mm"
include "f1oen3g.mm"
include "syl2anc.mm"

theorem oien
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


  assert |- ( ( A e. V /\ R We A ) -> dom F ~~ A )

  proof
    cA
    cV
    wcel
    #
    cA
    cR
    wwe
    #
    wa
    #
    cF
    cvv
    wcel
    #
    cF
    cdm
    #
    cA
    cF
    wf1o
    #
    @4
    cA
    cen
    wbr
    @0
    @3
    @1
    cA
    cR
    cF
    cV
    oicl.1
    oiexg
    adantr
    @2
    @4
    cA
    cep
    cR
    cF
    wiso
    @5
    cA
    cR
    cF
    cV
    oicl.1
    oiiso
    @4
    cA
    cep
    cR
    cF
    isof1o
    syl
    @4
    cA
    cF
    cvv
    f1oen3g
    syl2anc
end
