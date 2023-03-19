include "crngo.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cidl.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "cint.mm"
include "c1st.mm"
include "crn.mm"
include "cgi.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "c2nd.mm"
include "wa.mm"
include "cuni.mm"
include "intssuni.mm"
include "3ad2ant2.mm"
include "ssel2.mm"
include "eqid.mm"
include "idlss.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "3adant2.mm"
include "unissb.mm"
include "sylibr.mm"
include "sstrd.mm"
include "idl0cl.mm"
include "fvex.mm"
include "elint2.mm"
include "vex.mm"
include "r19.26.mm"
include "wi.mm"
include "idladdcl.mm"
include "ex.mm"
include "ralimdva.mm"
include "ovex.mm"
include "syl6ibr.mm"
include "syl5bir.mm"
include "expdimp.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "idllmulcl.mm"
include "anass1rs.mm"
include "an32s.mm"
include "an4s.mm"
include "imp.mm"
include "idlrmulcl.mm"
include "jca.mm"
include "wb.mm"
include "isidl.mm"
include "3ad2ant1.mm"
include "mpbir3and.mm"

theorem intidl
  let cC: class C
  let cR: class R
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( R e. RingOps /\ C =/= (/) /\ C C_ ( Idl ` R ) ) -> |^| C e. ( Idl ` R ) )

  proof
    cR
    crngo
    wcel
    #
    cC
    c0
    wne
    #
    cC
    cR
    cidl
    cfv
    #
    wss
    #
    w3a
    #
    cC
    cint
    #
    @2
    wcel
    #
    @5
    cR
    c1st
    cfv
    #
    crn
    #
    wss
    #
    @7
    cgi
    cfv
    #
    @5
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    @7
    co
    #
    @5
    wcel
    #
    vy
    @5
    wral
    #
    vz
    cv
    #
    @12
    cR
    c2nd
    cfv
    #
    co
    #
    @5
    wcel
    #
    @12
    @17
    @18
    co
    #
    @5
    wcel
    #
    wa
    #
    vz
    @8
    wral
    #
    wa
    #
    vx
    @5
    wral
    #
    @4
    @5
    cC
    cuni
    #
    @8
    @1
    @0
    @5
    @27
    wss
    @3
    cC
    intssuni
    3ad2ant2
    @4
    vi
    cv
    #
    @8
    wss
    #
    vi
    cC
    wral
    #
    @27
    @8
    wss
    @0
    @3
    @30
    @1
    @0
    @3
    wa
    #
    @29
    vi
    cC
    @0
    @3
    @28
    cC
    wcel
    #
    @29
    @3
    @32
    wa
    #
    @0
    @28
    @2
    wcel
    #
    @29
    cC
    @2
    @28
    ssel2
    #
    cR
    @7
    @28
    @8
    @7
    eqid
    #
    @8
    eqid
    #
    idlss
    sylan2
    anassrs
    ralrimiva
    3adant2
    vi
    cC
    @8
    unissb
    sylibr
    sstrd
    @0
    @3
    @11
    @1
    @31
    @10
    @28
    wcel
    #
    vi
    cC
    wral
    @11
    @31
    @38
    vi
    cC
    @0
    @3
    @32
    @38
    @33
    @0
    @34
    @38
    @35
    cR
    @7
    @28
    @10
    @36
    @10
    eqid
    #
    idl0cl
    sylan2
    anassrs
    ralrimiva
    vi
    @10
    cC
    @7
    cgi
    fvex
    elint2
    sylibr
    3adant2
    @0
    @3
    @26
    @1
    @31
    @25
    vx
    @5
    @12
    @5
    wcel
    @12
    @28
    wcel
    #
    vi
    cC
    wral
    #
    @31
    @25
    vi
    @12
    cC
    vx
    vex
    elint2
    @31
    @41
    @25
    @31
    @41
    wa
    #
    @16
    @24
    @42
    @15
    vy
    @5
    @13
    @5
    wcel
    @13
    @28
    wcel
    #
    vi
    cC
    wral
    #
    @42
    @15
    vi
    @13
    cC
    vy
    vex
    elint2
    @31
    @41
    @44
    @15
    @41
    @44
    wa
    @40
    @43
    wa
    #
    vi
    cC
    wral
    #
    @31
    @15
    @40
    @43
    vi
    cC
    r19.26
    @31
    @46
    @14
    @28
    wcel
    #
    vi
    cC
    wral
    @15
    @31
    @45
    @47
    vi
    cC
    @0
    @3
    @32
    @45
    @47
    wi
    #
    @33
    @0
    @34
    @48
    @35
    @0
    @34
    wa
    #
    @45
    @47
    @12
    @13
    cR
    @7
    @28
    @36
    idladdcl
    ex
    sylan2
    anassrs
    ralimdva
    vi
    @14
    cC
    @12
    @13
    @7
    ovex
    elint2
    syl6ibr
    syl5bir
    expdimp
    syl5bi
    ralrimiv
    @42
    @23
    vz
    @8
    @31
    @17
    @8
    wcel
    #
    @41
    @23
    @31
    @50
    wa
    #
    @41
    wa
    #
    @20
    @22
    @52
    @19
    @28
    wcel
    #
    vi
    cC
    wral
    #
    @20
    @51
    @41
    @54
    @51
    @40
    @53
    vi
    cC
    @31
    @50
    @32
    @40
    @53
    wi
    #
    @0
    @50
    @3
    @32
    @55
    @33
    @0
    @50
    wa
    #
    @34
    @55
    @35
    @0
    @34
    @50
    @55
    @49
    @50
    wa
    #
    @40
    @53
    @49
    @40
    @50
    @53
    @12
    @17
    cR
    @7
    @18
    @28
    @8
    @36
    @18
    eqid
    #
    @37
    idllmulcl
    anass1rs
    ex
    an32s
    sylan2
    an4s
    anassrs
    ralimdva
    imp
    vi
    @19
    cC
    @17
    @12
    @18
    ovex
    elint2
    sylibr
    @52
    @21
    @28
    wcel
    #
    vi
    cC
    wral
    #
    @22
    @51
    @41
    @60
    @51
    @40
    @59
    vi
    cC
    @31
    @50
    @32
    @40
    @59
    wi
    #
    @0
    @50
    @3
    @32
    @61
    @33
    @56
    @34
    @61
    @35
    @0
    @34
    @50
    @61
    @57
    @40
    @59
    @49
    @40
    @50
    @59
    @12
    @17
    cR
    @7
    @18
    @28
    @8
    @36
    @58
    @37
    idlrmulcl
    anass1rs
    ex
    an32s
    sylan2
    an4s
    anassrs
    ralimdva
    imp
    vi
    @21
    cC
    @12
    @17
    @18
    ovex
    elint2
    sylibr
    jca
    an32s
    ralrimiva
    jca
    ex
    syl5bi
    ralrimiv
    3adant2
    @0
    @1
    @6
    @9
    @11
    @26
    w3a
    wb
    @3
    vx
    vy
    vz
    cR
    @7
    @18
    @5
    @8
    @10
    @36
    @58
    @37
    @39
    isidl
    3ad2ant1
    mpbir3and
end
