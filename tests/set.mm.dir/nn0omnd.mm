include "crefld.mm"
include "cn0.mm"
include "cress.mm"
include "co.mm"
include "ccnfld.mm"
include "comnd.mm"
include "cr.mm"
include "df-refld.mm"
include "oveq1i.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "reex.mm"
include "nn0ssre.mm"
include "ressabs.mm"
include "mp2an.mm"
include "eqtri.mm"
include "cmnd.mm"
include "cofld.mm"
include "reofld.mm"
include "corng.mm"
include "cogrp.mm"
include "cfield.mm"
include "isofld.mm"
include "simprbi.mm"
include "orngogrp.mm"
include "cgrp.mm"
include "isogrp.mm"
include "3syl.mm"
include "ax-mp.mm"
include "csubmnd.mm"
include "cfv.mm"
include "nn0subm.mm"
include "eqid.mm"
include "submmnd.mm"
include "eqeltri.mm"
include "submomnd.mm"
include "eqeltrri.mm"

theorem nn0omnd



  assert |- ( CCfld |`s NN0 ) e. oMnd

  proof
    crefld
    cn0
    cress
    co
    #
    ccnfld
    cn0
    cress
    co
    #
    comnd
    @0
    ccnfld
    cr
    cress
    co
    #
    cn0
    cress
    co
    #
    @1
    crefld
    @2
    cn0
    cress
    df-refld
    oveq1i
    cr
    cvv
    wcel
    cn0
    cr
    wss
    @3
    @1
    wceq
    reex
    nn0ssre
    cr
    cn0
    ccnfld
    cvv
    ressabs
    mp2an
    eqtri
    #
    crefld
    comnd
    wcel
    #
    @0
    cmnd
    wcel
    @0
    comnd
    wcel
    crefld
    cofld
    wcel
    #
    @5
    reofld
    @6
    crefld
    corng
    wcel
    #
    crefld
    cogrp
    wcel
    #
    @5
    @6
    crefld
    cfield
    wcel
    @7
    crefld
    isofld
    simprbi
    crefld
    orngogrp
    @8
    crefld
    cgrp
    wcel
    @5
    crefld
    isogrp
    simprbi
    3syl
    ax-mp
    @0
    @1
    cmnd
    @4
    cn0
    ccnfld
    csubmnd
    cfv
    wcel
    @1
    cmnd
    wcel
    nn0subm
    cn0
    @1
    ccnfld
    @1
    eqid
    submmnd
    ax-mp
    eqeltri
    cn0
    crefld
    submomnd
    mp2an
    eqeltrri
end
