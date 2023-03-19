include "cop.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wbr.mm"
include "eldif.mm"
include "df-br.mm"
include "notbii.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem brdif
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S


  assert |- ( A ( R \ S ) B <-> ( A R B /\ -. A S B ) )

  proof
    cA
    cB
    cop
    #
    cR
    cS
    cdif
    #
    wcel
    @0
    cR
    wcel
    #
    @0
    cS
    wcel
    #
    wn
    #
    wa
    cA
    cB
    @1
    wbr
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cS
    wbr
    #
    wn
    #
    wa
    @0
    cR
    cS
    eldif
    cA
    cB
    @1
    df-br
    @5
    @2
    @7
    @4
    cA
    cB
    cR
    df-br
    @6
    @3
    cA
    cB
    cS
    df-br
    notbii
    anbi12i
    3bitr4i
end
