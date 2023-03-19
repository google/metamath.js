include "cprime.mm"
include "wcel.mm"
include "codd.mm"
include "wa.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "oddprmne2.mm"
include "oddprmge3.mm"
include "sylbi.mm"

theorem oddprmuzge3
  let cP: class P
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( P e. Prime /\ P e. Odd ) -> P e. ( ZZ>= ` 3 ) )

  proof
    cP
    cprime
    wcel
    cP
    codd
    wcel
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
    oddprmne2
    cP
    oddprmge3
    sylbi
end
