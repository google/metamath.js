include "csalg.mm"
include "wcel.mm"
include "w3a.mm"
include "cin.mm"
include "cuni.mm"
include "cdif.mm"
include "cun.mm"
include "eqidd.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "elssuni.mm"
include "adantl.mm"
include "sstrd.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "difindi.mm"
include "difeq2i.mm"
include "3eqtrd.mm"
include "simp1.mm"
include "saldifcl.mm"
include "3adant2.mm"
include "saluncl.mm"
include "syl3anc.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem salincl
  let cS: class S
  let cE: class E
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( S e. SAlg /\ E e. S /\ F e. S ) -> ( E i^i F ) e. S )

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
    cin
    #
    cS
    cuni
    #
    @5
    cE
    cdif
    #
    @5
    cF
    cdif
    #
    cun
    #
    cdif
    #
    cS
    @3
    @4
    @4
    @5
    @5
    @4
    cdif
    #
    cdif
    #
    @9
    @3
    @4
    eqidd
    @0
    @1
    @4
    @11
    wceq
    @2
    @0
    @1
    wa
    #
    @11
    @4
    @12
    @4
    @5
    wss
    @11
    @4
    wceq
    @12
    @4
    cE
    @5
    @4
    cE
    wss
    @12
    cE
    cF
    inss1
    a1i
    @1
    cE
    @5
    wss
    @0
    cE
    cS
    elssuni
    adantl
    sstrd
    @4
    @5
    dfss4
    sylib
    eqcomd
    3adant3
    @11
    @9
    wceq
    @3
    @10
    @8
    @5
    @5
    cE
    cF
    difindi
    difeq2i
    a1i
    3eqtrd
    @3
    @0
    @8
    cS
    wcel
    #
    @9
    cS
    wcel
    @0
    @1
    @2
    simp1
    #
    @3
    @0
    @6
    cS
    wcel
    #
    @7
    cS
    wcel
    #
    @13
    @14
    @0
    @1
    @15
    @2
    cS
    cE
    saldifcl
    3adant3
    @0
    @2
    @16
    @1
    cS
    cF
    saldifcl
    3adant2
    cS
    @6
    @7
    saluncl
    syl3anc
    cS
    @8
    saldifcl
    syl2anc
    eqeltrd
end
