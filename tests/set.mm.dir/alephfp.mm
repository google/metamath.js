include "com.mm"
include "cima.mm"
include "cuni.mm"
include "cale.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "con0.mm"
include "wrex.mm"
include "alephfplem4.mm"
include "wss.mm"
include "ccrd.mm"
include "wa.mm"
include "isinfcard.mm"
include "cardalephex.mm"
include "biimpa.mm"
include "sylbir.mm"
include "wn.mm"
include "alephle.mm"
include "alephon.mm"
include "onirri.mm"
include "wi.mm"
include "wfn.mm"
include "wfun.mm"
include "wb.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fnfun.mm"
include "eluniima.mm"
include "mp2b.mm"
include "alephsson.mm"
include "alephfplem3.mm"
include "sseldi.mm"
include "alephord2i.mm"
include "syl.mm"
include "csuc.mm"
include "alephfplem2.mm"
include "peano2.mm"
include "fnfvelrn.mm"
include "mpan.mm"
include "fnima.mm"
include "ax-mp.mm"
include "syl6eleqr.mm"
include "eqeltrrd.mm"
include "elssuni.mm"
include "sseld.mm"
include "syld.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "mpbii.mm"
include "mtoi.mm"
include "anim12i.mm"
include "word.mm"
include "eloni.mm"
include "onordi.mm"
include "ordtri4.mm"
include "sylancl.mm"
include "adantr.mm"
include "mpbird.mm"
include "eqeq2.mm"
include "adantl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "rexlimiva.mm"

theorem alephfp
  let cH: class H
  let vw: setvar w
  let vz: setvar z
  let vv: setvar v
  assume alephfplem.1: |- H = ( rec ( aleph , _om ) |` _om )


  assert |- ( aleph ` U. ( H " _om ) ) = U. ( H " _om )

  proof
    cH
    com
    cima
    #
    cuni
    #
    cale
    crn
    #
    wcel
    #
    @1
    vz
    cv
    #
    cale
    cfv
    #
    wceq
    #
    vz
    con0
    wrex
    #
    @1
    cale
    cfv
    #
    @1
    wceq
    #
    cH
    alephfplem.1
    alephfplem4
    @3
    com
    @1
    wss
    #
    @1
    ccrd
    cfv
    @1
    wceq
    #
    wa
    @7
    @1
    isinfcard
    @10
    @11
    @7
    vz
    @1
    cardalephex
    biimpa
    sylbir
    @6
    @9
    vz
    con0
    @4
    con0
    wcel
    #
    @6
    wa
    #
    @9
    @8
    @5
    wceq
    #
    @13
    @1
    @4
    cale
    @13
    @4
    @1
    @13
    @4
    @1
    wceq
    #
    @4
    @5
    wceq
    #
    @13
    @16
    @4
    @5
    wss
    #
    @4
    @5
    wcel
    #
    wn
    #
    wa
    #
    @12
    @17
    @6
    @19
    @4
    alephle
    @6
    @18
    @5
    @5
    wcel
    #
    @5
    @4
    alephon
    #
    onirri
    @6
    @4
    @1
    wcel
    #
    @5
    @1
    wcel
    #
    wi
    @18
    @21
    wi
    @23
    @4
    vv
    cv
    #
    cH
    cfv
    #
    wcel
    #
    vv
    com
    wrex
    #
    @24
    cH
    com
    wfn
    #
    cH
    wfun
    @23
    @28
    wb
    @29
    cale
    com
    crdg
    com
    cres
    #
    com
    wfn
    com
    cale
    frfnom
    com
    cH
    @30
    alephfplem.1
    fneq1i
    mpbir
    #
    com
    cH
    fnfun
    vv
    com
    @4
    cH
    eluniima
    mp2b
    @27
    @24
    vv
    com
    @25
    com
    wcel
    #
    @27
    @5
    @26
    cale
    cfv
    #
    wcel
    #
    @24
    @32
    @26
    con0
    wcel
    @27
    @34
    wi
    @32
    @2
    con0
    @26
    alephsson
    vv
    cH
    alephfplem.1
    alephfplem3
    sseldi
    @4
    @26
    alephord2i
    syl
    @32
    @33
    @1
    @5
    @32
    @33
    @0
    wcel
    @33
    @1
    wss
    @32
    @25
    csuc
    #
    cH
    cfv
    #
    @33
    @0
    vv
    cH
    alephfplem.1
    alephfplem2
    @32
    @35
    com
    wcel
    #
    @36
    @0
    wcel
    @25
    peano2
    @37
    @36
    cH
    crn
    #
    @0
    @29
    @37
    @36
    @38
    wcel
    @31
    com
    @35
    cH
    fnfvelrn
    mpan
    @29
    @0
    @38
    wceq
    @31
    com
    cH
    fnima
    ax-mp
    syl6eleqr
    syl
    eqeltrrd
    @33
    @0
    elssuni
    syl
    sseld
    syld
    rexlimiv
    sylbi
    @6
    @23
    @18
    @24
    @21
    @1
    @5
    @4
    eleq2
    @1
    @5
    @5
    eleq2
    imbi12d
    mpbii
    mtoi
    anim12i
    @12
    @16
    @20
    wb
    #
    @6
    @12
    @4
    word
    @5
    word
    @39
    @4
    eloni
    @5
    @22
    onordi
    @4
    @5
    ordtri4
    sylancl
    adantr
    mpbird
    @6
    @15
    @16
    wb
    @12
    @1
    @5
    @4
    eqeq2
    adantl
    mpbird
    eqcomd
    fveq2d
    @6
    @9
    @14
    wb
    @12
    @1
    @5
    @8
    eqeq2
    adantl
    mpbird
    rexlimiva
    mp2b
end
