include "csalg.mm"
include "wcel.mm"
include "w3a.mm"
include "cdif.mm"
include "cuni.mm"
include "cin.mm"
include "wceq.mm"
include "indif2.mm"
include "a1i.mm"
include "wss.mm"
include "elssuni.mm"
include "df-ss.mm"
include "sylib.mm"
include "difeq1d.mm"
include "3ad2ant2.mm"
include "eqtr2d.mm"
include "simp1.mm"
include "simp2.mm"
include "saldifcl.mm"
include "3adant2.mm"
include "salincl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem saldifcl2
  let cS: class S
  let cE: class E
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. SAlg /\ E e. S /\ F e. S ) -> ( E \ F ) e. S )

  proof
    cS
    csalg
    wcel
    #
    cE
    cS
    wcel
    #
    cF
    cS
    wcel
    #
    w3a
    #
    cE
    cF
    cdif
    #
    cE
    cS
    cuni
    #
    cF
    cdif
    #
    cin
    #
    cS
    @3
    @7
    cE
    @5
    cin
    #
    cF
    cdif
    #
    @4
    @7
    @9
    wceq
    @3
    cE
    @5
    cF
    indif2
    a1i
    @1
    @0
    @9
    @4
    wceq
    @2
    @1
    @8
    cE
    cF
    @1
    cE
    @5
    wss
    @8
    cE
    wceq
    cE
    cS
    elssuni
    cE
    @5
    df-ss
    sylib
    difeq1d
    3ad2ant2
    eqtr2d
    @3
    @0
    @1
    @6
    cS
    wcel
    #
    @7
    cS
    wcel
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @2
    @10
    @1
    cS
    cF
    saldifcl
    3adant2
    cS
    cE
    @6
    salincl
    syl3anc
    eqeltrd
end
