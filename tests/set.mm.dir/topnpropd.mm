include "cts.mm"
include "cfv.mm"
include "cbs.mm"
include "crest.mm"
include "co.mm"
include "ctopn.mm"
include "oveq12d.mm"
include "eqid.mm"
include "topnval.mm"
include "3eqtr3g.mm"

theorem topnpropd
  let wph: wff ph
  let cK: class K
  let cL: class L
  assume topnpropd.1: |- ( ph -> ( Base ` K ) = ( Base ` L ) )
  assume topnpropd.2: |- ( ph -> ( TopSet ` K ) = ( TopSet ` L ) )


  assert |- ( ph -> ( TopOpen ` K ) = ( TopOpen ` L ) )

  proof
    wph
    cK
    cts
    cfv
    #
    cK
    cbs
    cfv
    #
    crest
    co
    cL
    cts
    cfv
    #
    cL
    cbs
    cfv
    #
    crest
    co
    cK
    ctopn
    cfv
    cL
    ctopn
    cfv
    wph
    @0
    @2
    @1
    @3
    crest
    topnpropd.2
    topnpropd.1
    oveq12d
    @1
    @0
    cK
    @1
    eqid
    @0
    eqid
    topnval
    @3
    @2
    cL
    @3
    eqid
    @2
    eqid
    topnval
    3eqtr3g
end
