include "crecs.mm"
include "eqid.mm"
include "tfr2.mm"

theorem recsval
  let cA: class A
  let cF: class F


  assert |- ( A e. On -> ( recs ( F ) ` A ) = ( F ` ( recs ( F ) |` A ) ) )

  proof
    cA
    cF
    crecs
    #
    cF
    @0
    eqid
    tfr2
end
