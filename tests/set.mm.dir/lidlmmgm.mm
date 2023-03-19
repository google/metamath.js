include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmgm.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "cbs.mm"
include "wral.mm"
include "wceq.mm"
include "lidlbas.mm"
include "eleq1a.mm"
include "mpd.mm"
include "anim2i.mm"
include "adantr.mm"
include "wi.mm"
include "wss.mm"
include "lidlssbas.mm"
include "adantl.mm"
include "sseld.mm"
include "com12.mm"
include "impcom.mm"
include "simprr.mm"
include "eqid.mm"
include "lidlmcl.mm"
include "syl12anc.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "ismgm.mm"
include "mp1i.mm"
include "ressmulr.mm"
include "eqcomd.mm"
include "oveqdr.mm"
include "eleq1d.mm"
include "2ralbidva.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem lidlmmgm
  let cR: class R
  let cU: class U
  let cI: class I
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x
  assume lidlabl.l: |- L = ( LIdeal ` R )
  assume lidlabl.i: |- I = ( R |`s U )


  assert |- ( ( R e. Ring /\ U e. L ) -> ( mulGrp ` I ) e. Mgm )

  proof
    cR
    crg
    wcel
    #
    cU
    cL
    wcel
    #
    wa
    #
    cI
    cmgp
    cfv
    #
    cmgm
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cI
    cbs
    cfv
    #
    wcel
    #
    vb
    @9
    wral
    va
    @9
    wral
    #
    @2
    @10
    va
    vb
    @9
    @9
    @2
    @5
    @9
    wcel
    #
    @6
    @9
    wcel
    #
    wa
    #
    wa
    #
    @0
    @9
    cL
    wcel
    #
    wa
    #
    @5
    cR
    cbs
    cfv
    #
    wcel
    #
    @13
    @10
    @2
    @17
    @14
    @1
    @16
    @0
    @1
    @9
    cU
    wceq
    @16
    cR
    cU
    cI
    cL
    lidlabl.l
    lidlabl.i
    lidlbas
    cU
    cL
    @9
    eleq1a
    mpd
    anim2i
    adantr
    @14
    @2
    @19
    @12
    @2
    @19
    wi
    @13
    @2
    @12
    @19
    @2
    @9
    @18
    @5
    @1
    @9
    @18
    wss
    @0
    cR
    cU
    cI
    cL
    lidlabl.l
    lidlabl.i
    lidlssbas
    adantl
    sseld
    com12
    adantr
    impcom
    @2
    @12
    @13
    simprr
    @18
    cR
    @7
    cL
    @9
    @5
    @6
    lidlabl.l
    @18
    eqid
    @7
    eqid
    #
    lidlmcl
    syl12anc
    ralrimivva
    @2
    @4
    @5
    @6
    cI
    cmulr
    cfv
    #
    co
    #
    @9
    wcel
    #
    vb
    @9
    wral
    va
    @9
    wral
    #
    @11
    @3
    cvv
    wcel
    @4
    @24
    wb
    @2
    cI
    cmgp
    fvex
    va
    vb
    @9
    @3
    cvv
    @21
    @9
    cI
    @3
    @3
    eqid
    #
    @9
    eqid
    mgpbas
    cI
    @21
    @3
    @25
    @21
    eqid
    mgpplusg
    ismgm
    mp1i
    @2
    @23
    @10
    va
    vb
    @9
    @9
    @15
    @22
    @8
    @9
    @2
    @14
    va
    vb
    @21
    @7
    @1
    @21
    @7
    wceq
    @0
    @1
    @7
    @21
    cU
    cR
    cI
    @7
    cL
    lidlabl.i
    @20
    ressmulr
    eqcomd
    adantl
    oveqdr
    eleq1d
    2ralbidva
    bitrd
    mpbird
end
