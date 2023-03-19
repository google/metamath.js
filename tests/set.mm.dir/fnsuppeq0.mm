include "wfn.mm"
include "wcel.mm"
include "w3a.mm"
include "csupp.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cres.mm"
include "csn.mm"
include "cxp.mm"
include "wss.mm"
include "ss0b.mm"
include "cun.mm"
include "cvv.mm"
include "cin.mm"
include "wb.mm"
include "un0.mm"
include "uncom.mm"
include "eqtr3i.mm"
include "fneq2i.mm"
include "biimpi.mm"
include "3ad2ant1.mm"
include "fnex.mm"
include "3adant3.mm"
include "simp3.mm"
include "0in.mm"
include "a1i.mm"
include "fnsuppres.mm"
include "syl121anc.mm"
include "syl5bbr.mm"
include "fnresdm.mm"
include "eqeq1d.mm"
include "bitrd.mm"

theorem fnsuppeq0
  let cA: class A
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  let va: setvar a
  let cB: class B


  assert |- ( ( F Fn A /\ A e. W /\ Z e. V ) -> ( ( F supp Z ) = (/) <-> F = ( A X. { Z } ) ) )

  proof
    cF
    cA
    wfn
    #
    cA
    cW
    wcel
    #
    cZ
    cV
    wcel
    #
    w3a
    #
    cF
    cZ
    csupp
    co
    #
    c0
    wceq
    #
    cF
    cA
    cres
    #
    cA
    cZ
    csn
    cxp
    #
    wceq
    #
    cF
    @7
    wceq
    @5
    @4
    c0
    wss
    #
    @3
    @8
    @4
    ss0b
    @3
    cF
    c0
    cA
    cun
    #
    wfn
    #
    cF
    cvv
    wcel
    #
    @2
    c0
    cA
    cin
    c0
    wceq
    #
    @9
    @8
    wb
    @0
    @1
    @11
    @2
    @0
    @11
    cA
    @10
    cF
    cA
    c0
    cun
    cA
    @10
    cA
    un0
    cA
    c0
    uncom
    eqtr3i
    fneq2i
    biimpi
    3ad2ant1
    @0
    @1
    @12
    @2
    cA
    cW
    cF
    fnex
    3adant3
    @0
    @1
    @2
    simp3
    @13
    @3
    cA
    0in
    a1i
    c0
    cA
    cF
    cV
    cvv
    cZ
    fnsuppres
    syl121anc
    syl5bbr
    @3
    @6
    cF
    @7
    @0
    @1
    @6
    cF
    wceq
    @2
    cA
    cF
    fnresdm
    3ad2ant1
    eqeq1d
    bitrd
end
