include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "eldifsn.mm"
include "oddprmge3.mm"
include "sylbir.mm"

theorem prmn2uzge3OLD
  let cP: class P


  assert |- ( ( P e. Prime /\ P =/= 2 ) -> P e. ( ZZ>= ` 3 ) )

  proof
    cP
    cprime
    wcel
    cP
    c2
    wne
    wa
    cP
    cprime
    c2
    csn
    cdif
    wcel
    cP
    c3
    cuz
    cfv
    wcel
    cP
    cprime
    c2
    eldifsn
    cP
    oddprmge3
    sylbir
end
