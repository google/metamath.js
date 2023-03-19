include "cii.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "crest.mm"
include "eqid.mm"
include "dfii3.mm"
include "resstopn.mm"
include "eqtri.mm"

theorem dfii4
  let cI: class I
  assume dfii4.1: |- I = ( CCfld |`s ( 0 [,] 1 ) )


  assert |- II = ( TopOpen ` I )

  proof
    cii
    ccnfld
    ctopn
    cfv
    #
    cc0
    c1
    cicc
    co
    #
    crest
    co
    cI
    ctopn
    cfv
    @0
    @0
    eqid
    #
    dfii3
    @1
    cI
    @0
    ccnfld
    dfii4.1
    @2
    resstopn
    eqtri
end
