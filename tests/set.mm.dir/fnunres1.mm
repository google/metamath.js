include "wfn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "cdm.mm"
include "cres.mm"
include "fndm.mm"
include "3ad2ant1.mm"
include "reseq2d.mm"
include "wrel.mm"
include "fnrel.mm"
include "3ad2ant2.mm"
include "ineq12d.mm"
include "simp3.mm"
include "eqtrd.mm"
include "funresdm1.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem fnunres1
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( ( F Fn A /\ G Fn B /\ ( A i^i B ) = (/) ) -> ( ( F u. G ) |` A ) = F )

  proof
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    cA
    cB
    cin
    #
    c0
    wceq
    #
    w3a
    #
    cF
    cG
    cun
    #
    cF
    cdm
    #
    cres
    #
    @5
    cA
    cres
    cF
    @4
    @6
    cA
    @5
    @0
    @1
    @6
    cA
    wceq
    @3
    cA
    cF
    fndm
    3ad2ant1
    #
    reseq2d
    @4
    cF
    wrel
    #
    @6
    cG
    cdm
    #
    cin
    #
    c0
    wceq
    @7
    cF
    wceq
    @0
    @1
    @9
    @3
    cA
    cF
    fnrel
    3ad2ant1
    @4
    @11
    @2
    c0
    @4
    @6
    cA
    @10
    cB
    @8
    @1
    @0
    @10
    cB
    wceq
    @3
    cB
    cG
    fndm
    3ad2ant2
    ineq12d
    @0
    @1
    @3
    simp3
    eqtrd
    cF
    cG
    funresdm1
    syl2anc
    eqtr3d
end
