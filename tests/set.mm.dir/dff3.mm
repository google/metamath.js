include "wf.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "wral.mm"
include "wa.mm"
include "fssxp.mm"
include "wcel.mm"
include "wex.mm"
include "wmo.mm"
include "cfv.mm"
include "cop.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "fdm.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "funfvop.mm"
include "syl2an2r.mm"
include "df-br.mm"
include "sylibr.mm"
include "fvex.mm"
include "breq2.mm"
include "spcev.mm"
include "syl.mm"
include "funmo.mm"
include "adantr.mm"
include "eu5.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "jca.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wrel.mm"
include "wal.mm"
include "cvv.mm"
include "xpss.mm"
include "sstr.mm"
include "mpan2.mm"
include "df-rel.mm"
include "wi.mm"
include "df-ral.mm"
include "eumo.mm"
include "imim2i.mm"
include "adantl.mm"
include "wn.mm"
include "ssel.mm"
include "syl5bi.mm"
include "opelxp1.mm"
include "syl6.mm"
include "exlimdv.mm"
include "con3d.mm"
include "exmo.mm"
include "ori.mm"
include "pm2.61d.mm"
include "ex.mm"
include "alimdv.mm"
include "imp.mm"
include "dffun6.mm"
include "dmss.mm"
include "dmxpss.mm"
include "syl6ss.mm"
include "weq.mm"
include "breq1.mm"
include "eubidv.mm"
include "rspccv.mm"
include "euex.mm"
include "vex.mm"
include "eldm.mm"
include "ssrdv.mm"
include "anim12i.mm"
include "eqss.mm"
include "df-fn.mm"
include "rnss.mm"
include "rnxpss.mm"
include "df-f.mm"
include "impbii.mm"

theorem dff3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B z
  disjoint F z
  assert |- ( F : A --> B <-> ( F C_ ( A X. B ) /\ A. x e. A E! y x F y ) )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    cA
    cB
    cxp
    #
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    vy
    weu
    #
    vx
    cA
    wral
    #
    wa
    #
    @0
    @2
    @7
    cA
    cB
    cF
    fssxp
    @0
    @6
    vx
    cA
    @0
    @3
    cA
    wcel
    #
    wa
    #
    @5
    vy
    wex
    #
    @5
    vy
    wmo
    #
    @6
    @10
    @3
    @3
    cF
    cfv
    #
    cF
    wbr
    #
    @11
    @10
    @3
    @13
    cop
    cF
    wcel
    #
    @14
    @0
    cF
    wfun
    #
    @9
    @3
    cF
    cdm
    #
    wcel
    #
    @15
    cA
    cB
    cF
    ffun
    #
    @0
    @18
    @9
    @0
    @17
    cA
    @3
    cA
    cB
    cF
    fdm
    eleq2d
    biimpar
    @3
    cF
    funfvop
    syl2an2r
    @3
    @13
    cF
    df-br
    sylibr
    @5
    @14
    vy
    @13
    @3
    cF
    fvex
    @4
    @13
    @3
    cF
    breq2
    spcev
    syl
    @0
    @12
    @9
    @0
    @16
    @12
    @19
    vy
    @3
    cF
    funmo
    syl
    adantr
    @5
    vy
    eu5
    sylanbrc
    ralrimiva
    jca
    @8
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wss
    #
    @0
    @8
    @16
    @17
    cA
    wceq
    #
    @20
    @8
    cF
    wrel
    #
    @12
    vx
    wal
    #
    @16
    @2
    @24
    @7
    @2
    cF
    cvv
    cvv
    cxp
    #
    wss
    #
    @24
    @2
    @1
    @26
    wss
    @27
    cA
    cB
    xpss
    cF
    @1
    @26
    sstr
    mpan2
    cF
    df-rel
    sylibr
    adantr
    @2
    @7
    @25
    @7
    @9
    @6
    wi
    #
    vx
    wal
    @2
    @25
    @6
    vx
    cA
    df-ral
    @2
    @28
    @12
    vx
    @2
    @28
    @12
    @2
    @28
    wa
    @9
    @12
    @28
    @9
    @12
    wi
    @2
    @6
    @12
    @9
    @5
    vy
    eumo
    imim2i
    adantl
    @2
    @9
    wn
    #
    @12
    wi
    @28
    @2
    @29
    @11
    wn
    @12
    @2
    @11
    @9
    @2
    @5
    @9
    vy
    @2
    @5
    @3
    @4
    cop
    #
    @1
    wcel
    #
    @9
    @5
    @30
    cF
    wcel
    @2
    @31
    @3
    @4
    cF
    df-br
    cF
    @1
    @30
    ssel
    syl5bi
    @3
    @4
    cA
    cB
    opelxp1
    syl6
    exlimdv
    con3d
    @11
    @12
    @5
    vy
    exmo
    ori
    syl6
    adantr
    pm2.61d
    ex
    alimdv
    syl5bi
    imp
    vx
    vy
    cF
    dffun6
    sylanbrc
    @8
    @17
    cA
    wss
    #
    cA
    @17
    wss
    #
    wa
    @23
    @2
    @32
    @7
    @33
    @2
    @17
    @1
    cdm
    cA
    cF
    @1
    dmss
    cA
    cB
    dmxpss
    syl6ss
    @7
    vz
    cA
    @17
    @7
    vz
    cv
    #
    cA
    wcel
    @34
    @4
    cF
    wbr
    #
    vy
    weu
    #
    @34
    @17
    wcel
    #
    @6
    @36
    vx
    @34
    cA
    vx
    vz
    weq
    @5
    @35
    vy
    @3
    @34
    @4
    cF
    breq1
    eubidv
    rspccv
    @36
    @35
    vy
    wex
    @37
    @35
    vy
    euex
    vy
    @34
    cF
    vz
    vex
    eldm
    sylibr
    syl6
    ssrdv
    anim12i
    @17
    cA
    eqss
    sylibr
    cF
    cA
    df-fn
    sylanbrc
    @2
    @22
    @7
    @2
    @21
    @1
    crn
    cB
    cF
    @1
    rnss
    cA
    cB
    rnxpss
    syl6ss
    adantr
    cA
    cB
    cF
    df-f
    sylanbrc
    impbii
end
