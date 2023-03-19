include "cds.mm"
include "cfv.mm"
include "cnx.mm"
include "cts.mm"
include "cmopn.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "fveq2d.mm"
include "dsid.mm"
include "wne.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "c9.mm"
include "9re.mm"
include "1nn.mm"
include "2nn0.mm"
include "9nn0.mm"
include "9lt10.mm"
include "declti.mm"
include "gtneii.mm"
include "dsndx.mm"
include "tsetndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "syl6reqr.mm"

theorem setsmsds
  let wph: wff ph
  let cD: class D
  let cK: class K
  let cM: class M
  let cX: class X
  assume setsms.x: |- ( ph -> X = ( Base ` M ) )
  assume setsms.d: |- ( ph -> D = ( ( dist ` M ) |` ( X X. X ) ) )
  assume setsms.k: |- ( ph -> K = ( M sSet <. ( TopSet ` ndx ) , ( MetOpen ` D ) >. ) )


  assert |- ( ph -> ( dist ` M ) = ( dist ` K ) )

  proof
    wph
    cK
    cds
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
    cds
    cfv
    cM
    cds
    cfv
    wph
    cK
    @2
    cds
    setsms.k
    fveq2d
    @1
    @0
    cds
    cM
    dsid
    cnx
    cds
    cfv
    #
    @0
    wne
    c1
    c2
    cdc
    #
    c9
    wne
    c9
    @4
    9re
    c1
    c2
    c9
    1nn
    2nn0
    9nn0
    9lt10
    declti
    gtneii
    @3
    @4
    @0
    c9
    dsndx
    tsetndx
    neeq12i
    mpbir
    setsnid
    syl6reqr
end
