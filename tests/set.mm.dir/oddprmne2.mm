include "cprime.mm"
include "wcel.mm"
include "codd.mm"
include "wa.mm"
include "c2.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wceq.mm"
include "ceven.mm"
include "cz.mm"
include "wb.mm"
include "prmz.mm"
include "zeo2ALTV.mm"
include "syl.mm"
include "evenprm2.mm"
include "bitr3d.mm"
include "nne.mm"
include "syl6bbr.mm"
include "con4bid.mm"
include "pm5.32i.mm"
include "eldifsn.mm"
include "bitr4i.mm"

theorem oddprmne2
  let cP: class P
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( P e. Prime /\ P e. Odd ) <-> P e. ( Prime \ { 2 } ) )

  proof
    cP
    cprime
    wcel
    #
    cP
    codd
    wcel
    #
    wa
    @0
    cP
    c2
    wne
    #
    wa
    cP
    cprime
    c2
    csn
    cdif
    wcel
    @0
    @1
    @2
    @0
    @1
    @2
    @0
    @1
    wn
    #
    cP
    c2
    wceq
    #
    @2
    wn
    @0
    cP
    ceven
    wcel
    #
    @3
    @4
    @0
    cP
    cz
    wcel
    @5
    @3
    wb
    cP
    prmz
    cP
    zeo2ALTV
    syl
    cP
    evenprm2
    bitr3d
    cP
    c2
    nne
    syl6bbr
    con4bid
    pm5.32i
    cP
    cprime
    c2
    eldifsn
    bitr4i
end
