include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "w3a.mm"
include "cbl.mm"
include "co.mm"
include "cxp.mm"
include "cres.mm"
include "cbnd.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "wss.mm"
include "simp1.mm"
include "cxr.mm"
include "rexr.mm"
include "blssm.mm"
include "syl3an3.mm"
include "xmetres2.mm"
include "syl2anc.mm"
include "adantr.mm"
include "rzal.mm"
include "adantl.mm"
include "isbndx.mm"
include "sylanbrc.mm"
include "wne.mm"
include "simpl2.mm"
include "simpl3.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "xbln0.mm"
include "biimpa.mm"
include "elrpd.mm"
include "blcntr.mm"
include "syl3anc.mm"
include "cin.mm"
include "elind.mm"
include "rexrd.mm"
include "eqid.mm"
include "blres.mm"
include "inidm.mm"
include "syl6req.mm"
include "rspceov.mm"
include "isbnd2.mm"
include "simpld.mm"
include "pm2.61dane.mm"

theorem blbnd
  let cR: class R
  let cM: class M
  let cX: class X
  let cY: class Y
  let vd: setvar d
  let vm: setvar m
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  let cP: class P
  let cS: class S


  assert |- ( ( M e. ( *Met ` X ) /\ Y e. X /\ R e. RR ) -> ( M |` ( ( Y ( ball ` M ) R ) X. ( Y ( ball ` M ) R ) ) ) e. ( Bnd ` ( Y ( ball ` M ) R ) ) )

  proof
    cM
    cX
    cxmt
    cfv
    wcel
    #
    cY
    cX
    wcel
    #
    cR
    cr
    wcel
    #
    w3a
    #
    cM
    cY
    cR
    cM
    cbl
    cfv
    co
    #
    @4
    cxp
    cres
    #
    @4
    cbnd
    cfv
    wcel
    #
    @4
    c0
    @3
    @4
    c0
    wceq
    #
    wa
    @5
    @4
    cxmt
    cfv
    wcel
    #
    @4
    vx
    cv
    vr
    cv
    @5
    cbl
    cfv
    #
    co
    wceq
    vr
    crp
    wrex
    #
    vx
    @4
    wral
    #
    @6
    @3
    @8
    @7
    @3
    @0
    @4
    cX
    wss
    #
    @8
    @0
    @1
    @2
    simp1
    #
    @2
    @0
    @1
    cR
    cxr
    wcel
    #
    @12
    cR
    rexr
    #
    cM
    cY
    cR
    cX
    blssm
    syl3an3
    cM
    @4
    cX
    xmetres2
    syl2anc
    #
    adantr
    @7
    @11
    @3
    @10
    vx
    @4
    rzal
    adantl
    vx
    @5
    @4
    vr
    isbndx
    sylanbrc
    @3
    @4
    c0
    wne
    #
    wa
    #
    @6
    @17
    @18
    @8
    @10
    vx
    @4
    wrex
    #
    @6
    @17
    wa
    @3
    @8
    @17
    @16
    adantr
    @18
    cY
    @4
    wcel
    #
    cR
    crp
    wcel
    #
    @4
    cY
    cR
    @9
    co
    #
    wceq
    @19
    @18
    @0
    @1
    @21
    @20
    @3
    @0
    @17
    @13
    adantr
    #
    @0
    @1
    @2
    @17
    simpl2
    #
    @18
    cR
    @0
    @1
    @2
    @17
    simpl3
    #
    @3
    @17
    cc0
    cR
    clt
    wbr
    #
    @2
    @0
    @1
    @14
    @17
    @26
    wb
    @15
    cM
    cY
    cR
    cX
    xbln0
    syl3an3
    biimpa
    elrpd
    #
    cM
    cY
    cR
    cX
    blcntr
    syl3anc
    #
    @27
    @18
    @22
    @4
    @4
    cin
    #
    @4
    @18
    @0
    cY
    cX
    @4
    cin
    wcel
    @14
    @22
    @29
    wceq
    @23
    @18
    cX
    @4
    cY
    @24
    @28
    elind
    @18
    cR
    @25
    rexrd
    @5
    cM
    cY
    cR
    cX
    @4
    @5
    eqid
    blres
    syl3anc
    @4
    inidm
    syl6req
    vx
    vr
    @4
    crp
    cY
    cR
    @4
    @9
    rspceov
    syl3anc
    vx
    @5
    @4
    vr
    isbnd2
    sylanbrc
    simpld
    pm2.61dane
end
