include "crefld.mm"
include "cofld.mm"
include "wcel.mm"
include "cfield.mm"
include "corng.mm"
include "refld.mm"
include "crg.mm"
include "cogrp.mm"
include "cc0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "cr.mm"
include "wral.mm"
include "cdr.mm"
include "ccrg.mm"
include "isfld.mm"
include "simplbi.mm"
include "drngring.mm"
include "mp2b.mm"
include "cgrp.mm"
include "comnd.mm"
include "ringgrp.mm"
include "ax-mp.mm"
include "cmnd.mm"
include "ctos.mm"
include "caddc.mm"
include "grpmnd.mm"
include "retos.mm"
include "w3a.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "leadd1dd.mm"
include "3anassrs.mm"
include "ex.mm"
include "3impa.mm"
include "rgen3.mm"
include "rebase.mm"
include "replusg.mm"
include "rele2.mm"
include "isomnd.mm"
include "mpbir3an.mm"
include "isogrp.mm"
include "mpbir2an.mm"
include "mulge0.mm"
include "an4s.mm"
include "rgen2a.mm"
include "re0g.mm"
include "remulr.mm"
include "isorng.mm"
include "isofld.mm"

theorem reofld
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- RRfld e. oField

  proof
    crefld
    cofld
    wcel
    crefld
    cfield
    wcel
    #
    crefld
    corng
    wcel
    #
    refld
    @1
    crefld
    crg
    wcel
    #
    crefld
    cogrp
    wcel
    #
    cc0
    va
    cv
    #
    cle
    wbr
    #
    cc0
    vb
    cv
    #
    cle
    wbr
    #
    wa
    #
    cc0
    @4
    @6
    cmul
    co
    cle
    wbr
    #
    wi
    #
    vb
    cr
    wral
    va
    cr
    wral
    @0
    crefld
    cdr
    wcel
    #
    @2
    refld
    @0
    @11
    crefld
    ccrg
    wcel
    crefld
    isfld
    simplbi
    crefld
    drngring
    mp2b
    #
    @3
    crefld
    cgrp
    wcel
    #
    crefld
    comnd
    wcel
    #
    @2
    @13
    @12
    crefld
    ringgrp
    ax-mp
    #
    @14
    crefld
    cmnd
    wcel
    #
    crefld
    ctos
    wcel
    @4
    @6
    cle
    wbr
    #
    @4
    vc
    cv
    #
    caddc
    co
    @6
    @18
    caddc
    co
    cle
    wbr
    #
    wi
    #
    vc
    cr
    wral
    vb
    cr
    wral
    va
    cr
    wral
    @13
    @16
    @15
    crefld
    grpmnd
    ax-mp
    retos
    @20
    va
    vb
    vc
    cr
    cr
    cr
    @4
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @18
    cr
    wcel
    #
    @20
    @21
    @22
    wa
    #
    @23
    wa
    @17
    @19
    @21
    @22
    @23
    @17
    @19
    @21
    @22
    @23
    @17
    w3a
    #
    wa
    @4
    @6
    @18
    @21
    @25
    simpl
    @21
    @22
    @23
    @17
    simpr1
    @21
    @22
    @23
    @17
    simpr2
    @21
    @22
    @23
    @17
    simpr3
    leadd1dd
    3anassrs
    ex
    3impa
    rgen3
    cr
    caddc
    cle
    crefld
    va
    vb
    vc
    rebase
    replusg
    rele2
    isomnd
    mpbir3an
    crefld
    isogrp
    mpbir2an
    @10
    va
    vb
    cr
    @24
    @8
    @9
    @21
    @5
    @22
    @7
    @9
    @4
    @6
    mulge0
    an4s
    ex
    rgen2a
    cr
    crefld
    cmul
    cle
    cc0
    va
    vb
    rebase
    re0g
    remulr
    rele2
    isorng
    mpbir3an
    crefld
    isofld
    mpbir2an
end
