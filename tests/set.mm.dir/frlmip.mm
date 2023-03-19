include "wcel.mm"
include "wa.mm"
include "cip.mm"
include "cfv.mm"
include "csra.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "cbs.mm"
include "cress.mm"
include "cmap.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "cfrlm.mm"
include "crglmod.mm"
include "cpws.mm"
include "wceq.mm"
include "eqid.mm"
include "frlmpws.mm"
include "ancoms.mm"
include "csca.mm"
include "ressid.mm"
include "eqidd.mm"
include "wss.mm"
include "eqimssi.mm"
include "a1i.mm"
include "srasca.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "adantl.mm"
include "cvv.mm"
include "fvex.mm"
include "rlmval.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "oveq1i.mm"
include "pwsval.mm"
include "mpan.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "ressip.mm"
include "ax-mp.mm"
include "simpr.mm"
include "snex.mm"
include "xpexg.mm"
include "mpan2.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "snnz.mm"
include "dmxp.mm"
include "prdsip.mm"
include "cixp.mm"
include "prdsbas.mm"
include "srabase.mm"
include "fvconst2.mm"
include "3eqtr4rd.mm"
include "ixpeq2dva.mm"
include "eqeltri.mm"
include "ixpconstg.mm"
include "3eqtrd.mm"
include "cmulr.mm"
include "sraip.mm"
include "syl5req.mm"
include "oveqd.mm"
include "mpteq2ia.mm"
include "oveq2i.mm"
include "mpt2eq123dv.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "eqtr2d.mm"

theorem frlmip
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  assume frlmphl.y: |- Y = ( R freeLMod I )
  assume frlmphl.b: |- B = ( Base ` R )
  assume frlmphl.t: |- .x. = ( .r ` R )

  disjoint B f
  disjoint B g
  disjoint B x
  disjoint f g
  disjoint f x
  disjoint g x
  disjoint I f
  disjoint I g
  disjoint I x
  disjoint R f
  disjoint R g
  disjoint R x
  disjoint V f
  disjoint V g
  disjoint V x
  disjoint W f
  disjoint W g
  disjoint W x
  assert |- ( ( I e. W /\ R e. V ) -> ( f e. ( B ^m I ) , g e. ( B ^m I ) |-> ( R gsum ( x e. I |-> ( ( f ` x ) .x. ( g ` x ) ) ) ) ) = ( .i ` Y ) )

  proof
    cI
    cW
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    #
    cY
    cip
    cfv
    cR
    cI
    cB
    cR
    csra
    cfv
    #
    cfv
    #
    csn
    #
    cxp
    #
    cprds
    co
    #
    cY
    cbs
    cfv
    #
    cress
    co
    #
    cip
    cfv
    #
    vf
    vg
    cB
    cI
    cmap
    co
    #
    @11
    cR
    vx
    cI
    vx
    cv
    #
    vf
    cv
    cfv
    #
    @12
    vg
    cv
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    @2
    cY
    @9
    cip
    @2
    cY
    cR
    cI
    cfrlm
    co
    #
    @9
    frlmphl.y
    @2
    @19
    cR
    crglmod
    cfv
    #
    cI
    cpws
    co
    #
    @19
    cbs
    cfv
    #
    cress
    co
    #
    @9
    @1
    @0
    @19
    @23
    wceq
    @22
    cR
    @19
    cI
    cV
    cW
    @19
    eqid
    @22
    eqid
    frlmpws
    ancoms
    @2
    @7
    @21
    @8
    @22
    cress
    @2
    @7
    @4
    csca
    cfv
    #
    @6
    cprds
    co
    #
    @21
    @1
    @7
    @25
    wceq
    @0
    @1
    cR
    @24
    @6
    cprds
    @1
    cR
    cB
    cress
    co
    cR
    @24
    cB
    cR
    cV
    frlmphl.b
    ressid
    @1
    @4
    cB
    cR
    @1
    @4
    eqidd
    cB
    cR
    cbs
    cfv
    #
    wss
    #
    @1
    cB
    @26
    frlmphl.b
    eqimssi
    #
    a1i
    srasca
    eqtr3d
    oveq1d
    adantl
    @0
    @21
    @25
    wceq
    #
    @1
    @4
    cvv
    wcel
    @0
    @29
    cB
    @3
    fvex
    #
    @4
    @24
    cI
    cvv
    cW
    @21
    @20
    @4
    cI
    cpws
    @20
    @26
    @3
    cfv
    @4
    cR
    rlmval
    cB
    @26
    @3
    frlmphl.b
    fveq2i
    eqtr4i
    oveq1i
    @24
    eqid
    pwsval
    mpan
    adantr
    eqtr4d
    @8
    @22
    wceq
    @2
    cY
    @19
    cbs
    frlmphl.y
    fveq2i
    a1i
    oveq12d
    eqtr4d
    syl5eq
    fveq2d
    @2
    @10
    @7
    cip
    cfv
    #
    @18
    @8
    cvv
    wcel
    @31
    @10
    wceq
    cY
    cbs
    fvex
    @8
    @7
    @9
    @31
    cvv
    @9
    eqid
    @31
    eqid
    #
    ressip
    ax-mp
    @2
    @31
    vf
    vg
    @7
    cbs
    cfv
    #
    @33
    cR
    vx
    cI
    @13
    @14
    @12
    @6
    cfv
    #
    cip
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    @18
    @2
    vx
    @33
    @7
    @6
    cR
    vf
    vg
    @31
    cI
    cV
    cvv
    @7
    eqid
    #
    @0
    @1
    simpr
    #
    @0
    @6
    cvv
    wcel
    #
    @1
    @0
    @5
    cvv
    wcel
    @41
    @4
    snex
    cI
    @5
    cW
    cvv
    xpexg
    mpan2
    adantr
    #
    @33
    eqid
    #
    @6
    cdm
    cI
    wceq
    #
    @2
    @5
    c0
    wne
    @44
    @4
    @30
    snnz
    cI
    @5
    dmxp
    ax-mp
    a1i
    #
    @32
    prdsip
    @2
    vf
    vg
    @33
    @33
    @38
    @11
    @11
    @17
    @2
    @33
    vx
    cI
    @34
    cbs
    cfv
    #
    cixp
    vx
    cI
    cB
    cixp
    #
    @11
    @2
    vx
    @33
    @7
    @6
    cR
    cI
    cV
    cvv
    @39
    @40
    @42
    @43
    @45
    prdsbas
    @2
    vx
    cI
    @46
    cB
    @12
    cI
    wcel
    #
    @46
    cB
    wceq
    @2
    @48
    @26
    @4
    cbs
    cfv
    cB
    @46
    @48
    @4
    cB
    cR
    @48
    @4
    eqidd
    @27
    @48
    @28
    a1i
    #
    srabase
    cB
    @26
    wceq
    @48
    frlmphl.b
    a1i
    @48
    @34
    @4
    cbs
    cI
    @4
    @12
    @30
    fvconst2
    #
    fveq2d
    3eqtr4rd
    adantl
    ixpeq2dva
    @0
    @47
    @11
    wceq
    #
    @1
    @0
    cB
    cvv
    wcel
    @51
    cB
    @26
    cvv
    frlmphl.b
    cR
    cbs
    fvex
    eqeltri
    vx
    cI
    cB
    cW
    cvv
    ixpconstg
    mpan2
    adantr
    3eqtrd
    #
    @52
    @38
    @17
    wceq
    @2
    @37
    @16
    cR
    cgsu
    vx
    cI
    @36
    @15
    @48
    @35
    c.x
    @13
    @14
    @48
    c.x
    cR
    cmulr
    cfv
    @35
    frlmphl.t
    @48
    @34
    cB
    cR
    @50
    @49
    sraip
    syl5req
    oveqd
    mpteq2ia
    oveq2i
    a1i
    mpt2eq123dv
    eqtrd
    syl5eqr
    eqtr2d
end
