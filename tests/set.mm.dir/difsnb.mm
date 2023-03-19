include "wcel.mm"
include "wn.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "difsn.mm"
include "wne.mm"
include "neldifsnd.mm"
include "nelne1.mm"
include "mpdan.mm"
include "necomd.mm"
include "necon2bi.mm"
include "impbii.mm"

theorem difsnb
  let cA: class A
  let cB: class B


  assert |- ( -. A e. B <-> ( B \ { A } ) = B )

  proof
    cA
    cB
    wcel
    #
    wn
    cB
    cA
    csn
    cdif
    #
    cB
    wceq
    cA
    cB
    difsn
    @0
    @1
    cB
    @0
    cB
    @1
    @0
    cA
    @1
    wcel
    wn
    cB
    @1
    wne
    @0
    cA
    cB
    neldifsnd
    cA
    cB
    @1
    nelne1
    mpdan
    necomd
    necon2bi
    impbii
end
