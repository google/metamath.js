include "crh.mm"
include "crg.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cur.mm"
include "wceq.mm"
include "cplusg.mm"
include "co.mm"
include "cmulr.mm"
include "wa.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "csb.mm"
include "cmpt2.mm"
include "cghm.mm"
include "cmgp.mm"
include "cmhm.mm"
include "cin.mm"
include "df-rnghom.mm"
include "wcel.mm"
include "wf.mm"
include "cab.mm"
include "cgrp.mm"
include "wb.mm"
include "ringgrp.mm"
include "eqid.mm"
include "isghm3.mm"
include "syl2an.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "fvex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "abbii.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "w3a.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "ringidval.mm"
include "ismhm.mm"
include "baib.mm"
include "3anass.mm"
include "bitr4i.mm"
include "ineq12d.mm"
include "ancom.mm"
include "r19.26-2.mm"
include "anass.mm"
include "3bitri.mm"
include "rabbii.mm"
include "oveq12.mm"
include "ancoms.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "adantr.mm"
include "anbi2d.mm"
include "rabeqbidv.mm"
include "csbie2.mm"
include "inrab.mm"
include "3eqtr4i.mm"
include "syl6reqr.mm"
include "mpt2eq3ia.mm"

theorem dfrhm2
  let vs: setvar s
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y

  disjoint r s
  disjoint r v
  disjoint r w
  disjoint f r
  disjoint r x
  disjoint r y
  disjoint s v
  disjoint s w
  disjoint f s
  disjoint s x
  disjoint s y
  disjoint v w
  disjoint f v
  disjoint v x
  disjoint v y
  disjoint f w
  disjoint w x
  disjoint w y
  disjoint f x
  disjoint f y
  disjoint x y
  assert |- RingHom = ( r e. Ring , s e. Ring |-> ( ( r GrpHom s ) i^i ( ( mulGrp ` r ) MndHom ( mulGrp ` s ) ) ) )

  proof
    crh
    vr
    vs
    crg
    crg
    vv
    vr
    cv
    #
    cbs
    cfv
    #
    vw
    vs
    cv
    #
    cbs
    cfv
    #
    @0
    cur
    cfv
    #
    vf
    cv
    #
    cfv
    @2
    cur
    cfv
    #
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    cplusg
    cfv
    #
    co
    @5
    cfv
    @8
    @5
    cfv
    #
    @9
    @5
    cfv
    #
    @2
    cplusg
    cfv
    #
    co
    wceq
    #
    @8
    @9
    @0
    cmulr
    cfv
    #
    co
    @5
    cfv
    @11
    @12
    @2
    cmulr
    cfv
    #
    co
    wceq
    #
    wa
    #
    vy
    vv
    cv
    #
    wral
    #
    vx
    @19
    wral
    #
    wa
    #
    vf
    vw
    cv
    #
    @19
    cmap
    co
    #
    crab
    #
    csb
    csb
    #
    cmpt2
    vr
    vs
    crg
    crg
    @0
    @2
    cghm
    co
    #
    @0
    cmgp
    cfv
    #
    @2
    cmgp
    cfv
    #
    cmhm
    co
    #
    cin
    #
    cmpt2
    vx
    vy
    vw
    vv
    vf
    vs
    vr
    df-rnghom
    vr
    vs
    crg
    crg
    @26
    @31
    @0
    crg
    wcel
    #
    @2
    crg
    wcel
    #
    wa
    #
    @31
    @14
    vy
    @1
    wral
    vx
    @1
    wral
    #
    vf
    @3
    @1
    cmap
    co
    #
    crab
    #
    @17
    vy
    @1
    wral
    vx
    @1
    wral
    #
    @7
    wa
    #
    vf
    @36
    crab
    #
    cin
    #
    @26
    @34
    @27
    @37
    @30
    @40
    @34
    @27
    @1
    @3
    @5
    wf
    #
    @35
    wa
    #
    vf
    cab
    #
    @37
    @34
    @43
    vf
    @27
    @32
    @0
    cgrp
    wcel
    @2
    cgrp
    wcel
    @5
    @27
    wcel
    @43
    wb
    @33
    @0
    ringgrp
    @2
    ringgrp
    vy
    vx
    @10
    @13
    @0
    @2
    @5
    @1
    @3
    @1
    eqid
    #
    @3
    eqid
    #
    @10
    eqid
    @13
    eqid
    isghm3
    syl2an
    abbi2dv
    @37
    @5
    @36
    wcel
    #
    @35
    wa
    #
    vf
    cab
    @44
    @35
    vf
    @36
    df-rab
    @48
    @43
    vf
    @47
    @42
    @35
    @3
    @1
    @5
    @2
    cbs
    fvex
    #
    @0
    cbs
    fvex
    #
    elmap
    #
    anbi1i
    abbii
    eqtri
    syl6eqr
    @34
    @30
    @42
    @38
    @7
    w3a
    #
    vf
    cab
    #
    @40
    @34
    @52
    vf
    @30
    @32
    @28
    cmnd
    wcel
    #
    @29
    cmnd
    wcel
    #
    @5
    @30
    wcel
    #
    @52
    wb
    @33
    @0
    @28
    @28
    eqid
    #
    ringmgp
    @2
    @29
    @29
    eqid
    #
    ringmgp
    @56
    @54
    @55
    wa
    @52
    vx
    vy
    @1
    @3
    @15
    @16
    @28
    @29
    @5
    @6
    @4
    @1
    @0
    @28
    @57
    @45
    mgpbas
    @3
    @2
    @29
    @58
    @46
    mgpbas
    @0
    @15
    @28
    @57
    @15
    eqid
    mgpplusg
    @2
    @16
    @29
    @58
    @16
    eqid
    mgpplusg
    @0
    @4
    @28
    @57
    @4
    eqid
    ringidval
    @2
    @6
    @29
    @58
    @6
    eqid
    ringidval
    ismhm
    baib
    syl2an
    abbi2dv
    @40
    @47
    @39
    wa
    #
    vf
    cab
    @53
    @39
    vf
    @36
    df-rab
    @59
    @52
    vf
    @59
    @42
    @39
    wa
    @52
    @47
    @42
    @39
    @51
    anbi1i
    @42
    @38
    @7
    3anass
    bitr4i
    abbii
    eqtri
    syl6eqr
    ineq12d
    @7
    @18
    vy
    @1
    wral
    #
    vx
    @1
    wral
    #
    wa
    #
    vf
    @36
    crab
    #
    @35
    @39
    wa
    #
    vf
    @36
    crab
    @26
    @41
    @62
    @64
    vf
    @36
    @62
    @61
    @7
    wa
    @35
    @38
    wa
    #
    @7
    wa
    @64
    @7
    @61
    ancom
    @61
    @65
    @7
    @14
    @17
    vx
    vy
    @1
    @1
    r19.26-2
    anbi1i
    @35
    @38
    @7
    anass
    3bitri
    rabbii
    vv
    vw
    @1
    @3
    @25
    @63
    @50
    @49
    @19
    @1
    wceq
    #
    @23
    @3
    wceq
    #
    wa
    #
    @22
    @62
    vf
    @24
    @36
    @67
    @66
    @24
    @36
    wceq
    @23
    @3
    @19
    @1
    cmap
    oveq12
    ancoms
    @68
    @21
    @61
    @7
    @66
    @21
    @61
    wb
    @67
    @20
    @60
    vx
    @19
    @1
    @18
    vy
    @19
    @1
    raleq
    raleqbi1dv
    adantr
    anbi2d
    rabeqbidv
    csbie2
    @35
    @39
    vf
    @36
    inrab
    3eqtr4i
    syl6reqr
    mpt2eq3ia
    eqtri
end
