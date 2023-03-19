include "crngo.mm"
include "wcel.mm"
include "csn.mm"
include "cidl.mm"
include "cfv.mm"
include "crn.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "c2nd.mm"
include "wa.mm"
include "eqid.mm"
include "rngo0cl.mm"
include "snssd.mm"
include "cgi.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snid.mm"
include "a1i.mm"
include "wceq.mm"
include "velsn.mm"
include "rngo0rid.mm"
include "mpdan.mm"
include "ovex.mm"
include "elsn.mm"
include "sylibr.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "rngorz.mm"
include "rngolz.mm"
include "jca.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "isidl.mm"
include "mpbir3and.mm"

theorem 0idl
  let cR: class R
  let cG: class G
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume 0idl.1: |- G = ( 1st ` R )
  assume 0idl.2: |- Z = ( GId ` G )


  assert |- ( R e. RingOps -> { Z } e. ( Idl ` R ) )

  proof
    cR
    crngo
    wcel
    #
    cZ
    csn
    #
    cR
    cidl
    cfv
    wcel
    @1
    cG
    crn
    #
    wss
    cZ
    @1
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    @1
    wcel
    #
    vy
    @1
    wral
    #
    vz
    cv
    #
    @4
    cR
    c2nd
    cfv
    #
    co
    #
    @1
    wcel
    #
    @4
    @9
    @10
    co
    #
    @1
    wcel
    #
    wa
    #
    vz
    @2
    wral
    #
    wa
    #
    vx
    @1
    wral
    @0
    cZ
    @2
    cR
    cG
    @2
    cZ
    0idl.1
    @2
    eqid
    #
    0idl.2
    rngo0cl
    #
    snssd
    @3
    @0
    cZ
    cZ
    cG
    cgi
    cfv
    cvv
    0idl.2
    cG
    cgi
    fvex
    eqeltri
    snid
    a1i
    @0
    @17
    vx
    @1
    @4
    @1
    wcel
    @4
    cZ
    wceq
    #
    @0
    @17
    vx
    cZ
    velsn
    @0
    @17
    @20
    cZ
    @5
    cG
    co
    #
    @1
    wcel
    #
    vy
    @1
    wral
    #
    @9
    cZ
    @10
    co
    #
    @1
    wcel
    #
    cZ
    @9
    @10
    co
    #
    @1
    wcel
    #
    wa
    #
    vz
    @2
    wral
    #
    wa
    @0
    @23
    @29
    @0
    @22
    vy
    @1
    @5
    @1
    wcel
    @5
    cZ
    wceq
    #
    @0
    @22
    vy
    cZ
    velsn
    @0
    @22
    @30
    cZ
    cZ
    cG
    co
    #
    @1
    wcel
    #
    @0
    @31
    cZ
    wceq
    #
    @32
    @0
    cZ
    @2
    wcel
    @33
    @19
    cZ
    cR
    cG
    @2
    cZ
    0idl.1
    @18
    0idl.2
    rngo0rid
    mpdan
    @31
    cZ
    cZ
    cZ
    cG
    ovex
    elsn
    sylibr
    @30
    @21
    @31
    @1
    @5
    cZ
    cZ
    cG
    oveq2
    eleq1d
    syl5ibrcom
    syl5bi
    ralrimiv
    @0
    @28
    vz
    @2
    @0
    @9
    @2
    wcel
    wa
    #
    @25
    @27
    @34
    @24
    cZ
    wceq
    @25
    @9
    cR
    cG
    @10
    @2
    cZ
    0idl.2
    @18
    0idl.1
    @10
    eqid
    #
    rngorz
    @24
    cZ
    @9
    cZ
    @10
    ovex
    elsn
    sylibr
    @34
    @26
    cZ
    wceq
    @27
    @9
    cR
    cG
    @10
    @2
    cZ
    0idl.2
    @18
    0idl.1
    @35
    rngolz
    @26
    cZ
    cZ
    @9
    @10
    ovex
    elsn
    sylibr
    jca
    ralrimiva
    jca
    @20
    @8
    @23
    @16
    @29
    @20
    @7
    @22
    vy
    @1
    @20
    @6
    @21
    @1
    @4
    cZ
    @5
    cG
    oveq1
    eleq1d
    ralbidv
    @20
    @15
    @28
    vz
    @2
    @20
    @12
    @25
    @14
    @27
    @20
    @11
    @24
    @1
    @4
    cZ
    @9
    @10
    oveq2
    eleq1d
    @20
    @13
    @26
    @1
    @4
    cZ
    @9
    @10
    oveq1
    eleq1d
    anbi12d
    ralbidv
    anbi12d
    syl5ibrcom
    syl5bi
    ralrimiv
    vx
    vy
    vz
    cR
    cG
    @10
    @1
    @2
    cZ
    0idl.1
    @35
    @18
    0idl.2
    isidl
    mpbir3and
end
