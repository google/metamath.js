include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "eldifi.mm"
include "oddn2prm.mm"
include "jca.mm"
include "simpl.mm"
include "wne.mm"
include "wceq.mm"
include "wi.mm"
include "z2even.mm"
include "breq2.mm"
include "mpbiri.mm"
include "a1i.mm"
include "con3dimp.mm"
include "neqned.mm"
include "nelsn.mm"
include "syl.mm"
include "eldifd.mm"
include "impbii.mm"

theorem nnoddn2prmb
  let cN: class N


  assert |- ( N e. ( Prime \ { 2 } ) <-> ( N e. Prime /\ -. 2 || N ) )

  proof
    cN
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    cN
    cprime
    wcel
    #
    c2
    cN
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    @1
    @2
    @4
    cN
    cprime
    @0
    eldifi
    cN
    oddn2prm
    jca
    @5
    cN
    cprime
    @0
    @2
    @4
    simpl
    @5
    cN
    c2
    wne
    cN
    @0
    wcel
    wn
    @5
    cN
    c2
    @2
    cN
    c2
    wceq
    #
    @3
    @6
    @3
    wi
    @2
    @6
    @3
    c2
    c2
    cdvds
    wbr
    z2even
    cN
    c2
    c2
    cdvds
    breq2
    mpbiri
    a1i
    con3dimp
    neqned
    cN
    c2
    nelsn
    syl
    eldifd
    impbii
end
