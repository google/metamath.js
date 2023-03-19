include "cfmtno.mm"
include "crn.mm"
include "cprime.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "prmdvdsfmtnof.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "breq2.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "adantl.mm"
include "id.mm"
include "wor.mm"
include "ltso.mm"
include "infexd.mm"
include "fvmptd.mm"
include "eqeqan12d.mm"
include "w3a.mm"
include "c2.mm"
include "cuz.mm"
include "cn0.mm"
include "wrex.mm"
include "fmtnorn.mm"
include "c3.mm"
include "fmtnoge3.mm"
include "uzuzle23.mm"
include "syl.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "mpbid.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "eqid.mm"
include "prmdvdsfmtnof1lem1.mm"
include "syl2an.mm"
include "prmdvdsfmtnof1lem2.mm"
include "syld.mm"
include "sylbid.mm"
include "rgen2a.mm"
include "dff13.mm"
include "mpbir2an.mm"

theorem prmdvdsfmtnof1
  let vf: setvar f
  let cF: class F
  let vp: setvar p
  let vg: setvar g
  let vh: setvar h
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x
  assume prmdvdsfmtnof.1: |- F = ( f e. ran FermatNo |-> inf ( { p e. Prime | p || f } , RR , < ) )

  disjoint f p
  disjoint F g
  disjoint F h
  disjoint g h
  disjoint f g
  disjoint f h
  disjoint f n
  disjoint g n
  disjoint g p
  disjoint h n
  disjoint h p
  disjoint n p
  disjoint k x
  assert |- F : ran FermatNo -1-1-> Prime

  proof
    cfmtno
    crn
    #
    cprime
    cF
    wf1
    @0
    cprime
    cF
    wf
    vg
    cv
    #
    cF
    cfv
    #
    vh
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vg
    vh
    weq
    #
    wi
    #
    vh
    @0
    wral
    vg
    @0
    wral
    vf
    cF
    vp
    prmdvdsfmtnof.1
    prmdvdsfmtnof
    @7
    vg
    vh
    @0
    @1
    @0
    wcel
    #
    @3
    @0
    wcel
    #
    wa
    #
    @5
    vp
    cv
    #
    @1
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    cr
    clt
    cinf
    #
    @11
    @3
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    cr
    clt
    cinf
    #
    wceq
    #
    @6
    @8
    @9
    @2
    @14
    @4
    @17
    @8
    vf
    @1
    @11
    vf
    cv
    #
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    cr
    clt
    cinf
    #
    @14
    @0
    cF
    cvv
    cF
    vf
    @0
    @22
    cmpt
    wceq
    #
    @8
    prmdvdsfmtnof.1
    a1i
    vf
    vg
    weq
    #
    @22
    @14
    wceq
    @8
    @24
    cr
    @21
    @13
    clt
    @24
    @20
    @12
    vp
    cprime
    @19
    @1
    @11
    cdvds
    breq2
    rabbidv
    infeq1d
    adantl
    @8
    id
    @8
    cr
    @13
    clt
    cr
    clt
    wor
    #
    @8
    ltso
    a1i
    infexd
    fvmptd
    @9
    vf
    @3
    @22
    @17
    @0
    cF
    cvv
    @23
    @9
    prmdvdsfmtnof.1
    a1i
    vf
    vh
    weq
    #
    @22
    @17
    wceq
    @9
    @26
    cr
    @21
    @16
    clt
    @26
    @20
    @15
    vp
    cprime
    @19
    @3
    @11
    cdvds
    breq2
    rabbidv
    infeq1d
    adantl
    @9
    id
    @9
    cr
    @16
    clt
    @25
    @9
    ltso
    a1i
    infexd
    fvmptd
    eqeqan12d
    @10
    @18
    @14
    cprime
    wcel
    @14
    @1
    cdvds
    wbr
    @14
    @3
    cdvds
    wbr
    w3a
    #
    @6
    @8
    @1
    c2
    cuz
    cfv
    #
    wcel
    #
    @3
    @28
    wcel
    #
    @18
    @27
    wi
    @9
    @8
    vn
    cv
    #
    cfmtno
    cfv
    #
    @1
    wceq
    #
    vn
    cn0
    wrex
    @29
    vn
    @1
    fmtnorn
    @33
    @29
    vn
    cn0
    @31
    cn0
    wcel
    #
    @33
    wa
    @32
    @28
    wcel
    #
    @29
    @34
    @35
    @33
    @34
    @32
    c3
    cuz
    cfv
    wcel
    @35
    @31
    fmtnoge3
    @32
    uzuzle23
    syl
    #
    adantr
    @33
    @35
    @29
    wb
    @34
    @32
    @1
    @28
    eleq1
    adantl
    mpbid
    rexlimiva
    sylbi
    @9
    @32
    @3
    wceq
    #
    vn
    cn0
    wrex
    @30
    vn
    @3
    fmtnorn
    @37
    @30
    vn
    cn0
    @34
    @37
    wa
    @35
    @30
    @34
    @35
    @37
    @36
    adantr
    @37
    @35
    @30
    wb
    @34
    @32
    @3
    @28
    eleq1
    adantl
    mpbid
    rexlimiva
    sylbi
    @1
    @3
    @14
    @17
    vp
    @14
    eqid
    @17
    eqid
    prmdvdsfmtnof1lem1
    syl2an
    @1
    @3
    @14
    prmdvdsfmtnof1lem2
    syld
    sylbid
    rgen2a
    vg
    vh
    @0
    cprime
    cF
    dff13
    mpbir2an
end
