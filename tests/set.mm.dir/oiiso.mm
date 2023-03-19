include "wcel.mm"
include "wse.mm"
include "wwe.mm"
include "cdm.mm"
include "cep.mm"
include "wiso.mm"
include "exse.mm"
include "ordtype.mm"
include "ancoms.mm"
include "sylan.mm"

theorem oiiso
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


  assert |- ( ( A e. V /\ R We A ) -> F Isom _E , R ( dom F , A ) )

  proof
    cA
    cV
    wcel
    cA
    cR
    wse
    #
    cA
    cR
    wwe
    #
    cF
    cdm
    cA
    cep
    cR
    cF
    wiso
    #
    cA
    cR
    cV
    exse
    @1
    @0
    @2
    cA
    cR
    cF
    oicl.1
    ordtype
    ancoms
    sylan
end
