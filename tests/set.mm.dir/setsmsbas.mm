include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cts.mm"
include "cmopn.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "baseid.mm"
include "wne.mm"
include "c1.mm"
include "c9.mm"
include "1re.mm"
include "1lt9.mm"
include "ltneii.mm"
include "basendx.mm"
include "tsetndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"

theorem setsmsbas
  let wph: wff ph
  let cD: class D
  let cK: class K
  let cM: class M
  let cX: class X
  assume setsms.x: |- ( ph -> X = ( Base ` M ) )
  assume setsms.d: |- ( ph -> D = ( ( dist ` M ) |` ( X X. X ) ) )
  assume setsms.k: |- ( ph -> K = ( M sSet <. ( TopSet ` ndx ) , ( MetOpen ` D ) >. ) )


  assert |- ( ph -> X = ( Base ` K ) )

  proof
    wph
    cM
    cbs
    cfv
    cM
    cnx
    cts
    cfv
    #
    cD
    cmopn
    cfv
    #
    cop
    csts
    co
    #
    cbs
    cfv
    cX
    cK
    cbs
    cfv
    @1
    @0
    cbs
    cM
    baseid
    cnx
    cbs
    cfv
    #
    @0
    wne
    c1
    c9
    wne
    c1
    c9
    1re
    1lt9
    ltneii
    @3
    c1
    @0
    c9
    basendx
    tsetndx
    neeq12i
    mpbir
    setsnid
    setsms.x
    wph
    cK
    @2
    cbs
    setsms.k
    fveq2d
    3eqtr4a
end
