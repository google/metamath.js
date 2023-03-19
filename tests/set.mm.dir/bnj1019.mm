include "w3a.mm"
include "wa.mm"
include "wex.mm"
include "w-bnj17.mm"
include "19.42v.mm"
include "bnj258.mm"
include "exbii.mm"
include "df-bnj17.mm"
include "3bitr4i.mm"

theorem bnj1019
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vp: setvar p

  disjoint ch p
  disjoint et p
  disjoint p th
  assert |- ( E. p ( th /\ ch /\ ta /\ et ) <-> ( th /\ ch /\ et /\ E. p ta ) )

  proof
    wth
    wch
    wet
    w3a
    #
    wta
    wa
    #
    vp
    wex
    @0
    wta
    vp
    wex
    #
    wa
    wth
    wch
    wta
    wet
    w-bnj17
    #
    vp
    wex
    wth
    wch
    wet
    @2
    w-bnj17
    @0
    wta
    vp
    19.42v
    @3
    @1
    vp
    wth
    wch
    wta
    wet
    bnj258
    exbii
    wth
    wch
    wet
    @2
    df-bnj17
    3bitr4i
end
